# FieldConfig

## Overview

The `field_config.py` module provides a type-safe and structured way to define field configurations for packets in verification environments. It replaces a traditional dictionary-based approach with proper class structures, offering better validation, auto-completion, and error detection.

## Features

- Object-oriented representation of field configurations
- Automatic validation of field properties and constraints
- Rich formatting and display capabilities
- Factory methods for common configurations
- Backward compatibility with dictionary-based configurations

## Classes

### FieldDefinition

A dataclass that defines a single field within a packet.

#### Attributes

- `name`: Field name
- `bits`: Width of the field in bits
- `default`: Default value for the field (default: 0)
- `format`: Display format ('hex', 'bin', 'dec') (default: 'hex')
- `display_width`: Width for display formatting (default: calculated based on bits)
- `active_bits`: Tuple of (msb, lsb) defining active bit range (default: full width)
- `description`: Human-readable description of the field (default: capitalized name)

#### Methods

- `to_dict()`: Convert to dictionary format for backward compatibility
- `from_dict()`: Create a FieldDefinition from a dictionary representation

### FieldConfig

Configuration class for managing all fields in a packet, maintaining field order and providing helper methods.

#### Constructor

```python
def __init__(self)
```

Initializes an empty field configuration.

#### Key Methods

- `add_field(field_def)`: Add a field to the configuration
- `add_field_dict(name, field_dict)`: Add a field from dictionary representation
- `remove_field(name)`: Remove a field from the configuration
- `get_field(name)`: Get a field definition by name
- `has_field(name)`: Check if a field exists
- `field_names()`: Get ordered list of field names
- `fields()`: Get ordered list of field definitions
- `items()`: Get name/definition pairs in order
- `to_dict()`: Convert to dictionary format
- `debug_str(indent=0)`: Return a formatted string representation
- `update_field_width(field_name, new_bits, update_active_bits=True)`: Update a field's bit width

#### Factory Methods

- `from_dict(field_dict)`: Create a FieldConfig from a dictionary
- `validate_and_create(field_dict, raise_errors=False)`: Validate and create from dictionary
- `create_data_only(data_width=32)`: Create a simple data-only field configuration
- `create_standard(addr_width=32, data_width=32)`: Create a standard address/data configuration
- `create_multi_data(addr_width=4, ctrl_width=4, data_width=8, num_data=2)`: Create a multi-data configuration

## Example Usage

### Creating Field Configurations

```python
from CocoTBFramework.components.field_config import FieldConfig, FieldDefinition

# Create a field configuration from scratch
config = FieldConfig()

# Add fields one by one
config.add_field(
    FieldDefinition(
        name="addr",
        bits=32,
        default=0,
        format="hex",
        description="Memory address"
    )
)

config.add_field(
    FieldDefinition(
        name="data",
        bits=64,
        default=0,
        format="hex",
        description="Data value"
    )
)

config.add_field(
    FieldDefinition(
        name="control",
        bits=8,
        default=0,
        format="bin",
        description="Control flags"
    )
)

# Print the configuration
print(config)
```

### Using Factory Methods

```python
# Create a standard address/data configuration
std_config = FieldConfig.create_standard(addr_width=64, data_width=32)
print(std_config)

# Create a multi-data configuration
multi_config = FieldConfig.create_multi_data(
    addr_width=8,
    ctrl_width=4,
    data_width=16,
    num_data=4
)
print(multi_config)
```

### Converting from Dictionary Format

```python
# Create from an existing dictionary configuration
dict_config = {
    "command": {"bits": 4, "format": "bin", "description": "Command type"},
    "address": {"bits": 32, "format": "hex", "description": "Memory address"},
    "length": {"bits": 16, "format": "dec", "description": "Transfer length"},
    "priority": {"bits": 2, "format": "bin", "description": "Transaction priority"}
}

# Convert to FieldConfig object
field_config = FieldConfig.from_dict(dict_config)

# Print the configuration
print(field_config)
```

### Updating Field Width

```python
# Create a standard configuration
config = FieldConfig.create_standard()

# Update the address width
config.update_field_width("addr", 64)

# Update the data width without changing active_bits
config.update_field_width("data", 128, update_active_bits=False)

# Print the updated configuration
print(config)
```

## Integration with Packet Class

The `FieldConfig` class is designed to work directly with the [Packet](packet.md) class:

```python
from CocoTBFramework.components.field_config import FieldConfig
from CocoTBFramework.components.packet import Packet

# Create a field configuration
config = FieldConfig.create_standard(addr_width=32, data_width=32)

# Create a packet with this configuration
packet = Packet(config, addr=0x1000, data=0xABCD1234)

# The packet will use the field definitions for formatting, validation, etc.
print(packet)
```

## Notes

- The `FieldConfig` class ensures type safety and validation compared to dictionary-based approaches
- Field display formats and widths are automatically calculated based on bit width
- Rich string representation provides better debugging capabilities
- Factory methods make it easy to create common configurations

## See Also

- [Packet](packet.md) - Uses FieldConfig for field management
- [ArbiterMonitor](arbiter_monitor.md) - May use FieldConfig for transaction definition

## Navigation

[↑ Components Index](index.md) | [↑ CocoTBFramework Index](../index.md)
