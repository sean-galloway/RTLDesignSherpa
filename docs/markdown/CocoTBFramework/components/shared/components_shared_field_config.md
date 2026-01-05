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

# field_config.py

Field Configuration Classes for GAXI Validation Framework that provide robust and type-safe field definitions, replacing dictionary-based approaches with proper class structures.

## Overview

The `field_config.py` module provides classes for defining field configurations with comprehensive validation, encoding support, and Rich table formatting. It supports both individual field definitions and complete packet configurations.

## Classes

### FieldDefinition

Definition of a single field within a packet using a dataclass structure.

#### Constructor

```python
@dataclass
class FieldDefinition:
    name: str
    bits: int
    default: int = 0
    format: str = "hex"
    display_width: int = 0
    active_bits: Optional[Tuple[int, int]] = None
    description: Optional[str] = None
    encoding: Optional[Dict[int, str]] = None
```

**Parameters:**
- `name`: Field name
- `bits`: Width of the field in bits
- `default`: Default value for the field (default: 0)
- `format`: Display format - 'hex', 'bin', or 'dec' (default: 'hex')
- `display_width`: Width for display formatting (auto-calculated if 0)
- `active_bits`: Tuple of (msb, lsb) defining active bit range (defaults to full width)
- `description`: Human-readable description (defaults to formatted name)
- `encoding`: Optional dictionary mapping values to state names

#### Methods

##### `to_dict() -> Dict[str, Any]`
Convert to dictionary format for backward compatibility.

```python
field_def = FieldDefinition("addr", 32, format="hex", description="Address field")
field_dict = field_def.to_dict()
# Returns: {'bits': 32, 'default': 0, 'format': 'hex', 'display_width': 8, ...}
```

##### `from_dict(name: str, field_dict: Dict[str, Any]) -> 'FieldDefinition'`
Create a FieldDefinition from a dictionary representation.

```python
field_dict = {'bits': 16, 'format': 'bin', 'default': 0xFF}
field_def = FieldDefinition.from_dict("data", field_dict)
```

#### Examples

```python
# Basic field definition
addr_field = FieldDefinition(
    name="addr",
    bits=32,
    format="hex",
    description="Memory address"
)

# Field with active bits (partial field)
status_field = FieldDefinition(
    name="status", 
    bits=8,
    active_bits=(7, 4),  # Only bits 7:4 are used
    format="bin",
    encoding={
        0x0: "IDLE",
        0x1: "ACTIVE", 
        0x2: "ERROR",
        0x3: "DONE"
    }
)

# Binary field with custom width
mask_field = FieldDefinition(
    name="mask",
    bits=16,
    format="bin",
    display_width=16,  # Show all 16 bits
    default=0xFFFF
)
```

### FieldConfig

Configuration of all fields in a packet, maintaining field order and providing helper methods for field manipulation.

#### Constructor

```python
FieldConfig()
```

Creates an empty field configuration. Fields are added using the `add_field()` method.

#### Methods

##### `add_field(field_def: FieldDefinition) -> 'FieldConfig'`
Add a field to the configuration.

**Parameters:**
- `field_def`: Field definition to add

**Returns:** Self for method chaining

```python
config = FieldConfig()
config.add_field(FieldDefinition("addr", 32, format="hex"))
config.add_field(FieldDefinition("data", 32, format="hex"))
```

##### `add_field_dict(name: str, field_dict: Dict[str, Any]) -> 'FieldConfig'`
Add a field from dictionary representation (for backward compatibility).

```python
config.add_field_dict("ctrl", {
    'bits': 8,
    'format': 'bin',
    'encoding': {0: 'READ', 1: 'WRITE'}
})
```

##### `remove_field(name: str) -> 'FieldConfig'`
Remove a field from the configuration.

```python
config.remove_field("unused_field")
```

##### `get_field(name: str) -> FieldDefinition`
Get a field definition by name.

**Raises:** KeyError if field doesn't exist

```python
addr_field = config.get_field("addr")
print(f"Address field has {addr_field.bits} bits")
```

##### `has_field(name: str) -> bool`
Check if a field exists in the configuration.

```python
if config.has_field("optional_field"):
    field = config.get_field("optional_field")
```

##### `field_names() -> List[str]`
Get ordered list of field names.

```python
names = config.field_names()
# Returns: ['addr', 'data', 'ctrl'] in definition order
```

##### `fields() -> List[FieldDefinition]`
Get ordered list of field definitions.

```python
for field_def in config.fields():
    print(f"{field_def.name}: {field_def.bits} bits")
```

##### `items()`
Get name/definition pairs in order, similar to dict.items().

```python
for name, field_def in config.items():
    print(f"{name} = {field_def.bits} bits, format={field_def.format}")
```

##### `get_total_bits() -> int`
Calculate the total number of bits across all fields.

```python
total = config.get_total_bits()
print(f"Total packet width: {total} bits")
```

##### `create_packet()`
Create a packet object compatible with the field configuration.

```python
packet = config.create_packet()
packet.addr = 0x1000
packet.data = 0xDEADBEEF
```

##### `debug_str(indent=0) -> str`
Return a formatted string representation using Rich tables.

```python
print(config.debug_str())
# Displays formatted table with all field information
```

#### Dictionary-like Interface

FieldConfig supports dictionary-like operations:

```python
# Length
num_fields = len(config)

# Iteration
for field_name in config:
    print(field_name)

# Membership testing
if "addr" in config:
    print("Address field exists")

# Direct access
addr_field = config["addr"]
```

#### Validation and Creation Methods

##### `validate_and_create(field_dict: Dict[str, Dict[str, Any]], raise_errors: bool = False) -> 'FieldConfig'`
Validate a dictionary-based field configuration and convert to FieldConfig object.

**Parameters:**
- `field_dict`: Dictionary mapping field names to field properties
- `raise_errors`: If True, raise exceptions for validation errors; if False, attempt to correct or warn

**Returns:** New validated FieldConfig instance

```python
# Define fields as dictionary
field_dict = {
    'addr': {'bits': 32, 'format': 'hex'},
    'data': {'bits': 32, 'format': 'hex'}, 
    'ctrl': {'bits': 8, 'format': 'bin', 'encoding': {0: 'READ', 1: 'WRITE'}}
}

# Validate and create
config = FieldConfig.validate_and_create(field_dict)
```

##### `from_dict(field_dict: Dict[str, Dict[str, Any]]) -> 'FieldConfig'`
Create a FieldConfig from a dictionary representation.

```python
config = FieldConfig.from_dict(field_dict)
```

#### Pre-built Configuration Methods

##### `create_data_only(data_width: int = 32) -> 'FieldConfig'`
Create a simple data-only field configuration.

```python
config = FieldConfig.create_data_only(64)  # 64-bit data field
```

##### `create_standard(addr_width: int = 32, data_width: int = 32) -> 'FieldConfig'`
Create a standard address/data field configuration.

```python
config = FieldConfig.create_standard(addr_width=32, data_width=64)
```

##### `create_multi_data(addr_width: int = 4, ctrl_width: int = 4, data_width: int = 8, num_data: int = 2) -> 'FieldConfig'`
Create a multi-data field configuration with addr, ctrl, and multiple data fields.

```python
# Creates: addr(4), ctrl(4), data0(8), data1(8)
config = FieldConfig.create_multi_data(addr_width=4, ctrl_width=4, data_width=8, num_data=2)
```

#### Field Manipulation Methods

##### `update_field_width(field_name: str, new_bits: int, update_active_bits: bool = True) -> 'FieldConfig'`
Update a field's bit width and optionally its active bits.

```python
config.update_field_width("addr", 64)  # Expand address to 64 bits
```

##### `set_encoding(field_name: str, encoding: Dict[int, str]) -> 'FieldConfig'`
Set an encoding dictionary for a field.

```python
config.set_encoding("status", {
    0: "IDLE",
    1: "ACTIVE", 
    2: "ERROR"
})
```

##### `add_encoding_value(field_name: str, value: int, state_name: str) -> 'FieldConfig'`
Add a single encoding value to a field.

```python
config.add_encoding_value("status", 3, "DONE")
```

## Usage Patterns

### Basic Field Configuration

```python
# Create configuration
config = FieldConfig()

# Add address field
config.add_field(FieldDefinition(
    name="addr",
    bits=32,
    format="hex",
    description="Memory address"
))

# Add data field  
config.add_field(FieldDefinition(
    name="data", 
    bits=32,
    format="hex",
    description="Data value"
))

# Add control field with encoding
config.add_field(FieldDefinition(
    name="cmd",
    bits=4,
    format="hex",
    encoding={
        0x0: "NOP",
        0x1: "READ", 
        0x2: "WRITE",
        0x3: "BURST"
    },
    description="Command type"
))

print(f"Total packet size: {config.get_total_bits()} bits")
```

### Configuration with Active Bits

```python
# Field where only certain bits are used
config.add_field(FieldDefinition(
    name="status",
    bits=32,
    active_bits=(15, 8),  # Only bits 15:8 are active
    format="hex",
    description="Status register"
))

# This is useful for registers where not all bits are used
```

### Validation and Error Correction

```python
# Dictionary with potential issues
problematic_config = {
    'addr': {'bits': 32, 'format': 'hex'},
    'data': {'bits': -5, 'format': 'invalid'},  # Invalid bits and format
    'ctrl': {}  # Missing required 'bits' field
}

# Validate and auto-correct
try:
    config = FieldConfig.validate_and_create(problematic_config, raise_errors=False)
    print("Configuration created with corrections")
except ValueError as e:
    print(f"Validation failed: {e}")
```

### Dynamic Field Configuration

```python
class ConfigBuilder:
    def __init__(self):
        self.config = FieldConfig()
    
    def add_address_field(self, width=32):
        self.config.add_field(FieldDefinition("addr", width, format="hex"))
        return self
    
    def add_data_fields(self, count=1, width=32):
        for i in range(count):
            self.config.add_field(FieldDefinition(f"data{i}", width, format="hex"))
        return self
    
    def add_control_field(self, width=8, commands=None):
        encoding = commands or {0: "NOP", 1: "READ", 2: "WRITE"}
        self.config.add_field(FieldDefinition("ctrl", width, format="bin", encoding=encoding))
        return self
    
    def build(self):
        return self.config

# Usage
config = (ConfigBuilder()
          .add_address_field(32)
          .add_data_fields(count=2, width=64)
          .add_control_field(width=4)
          .build())
```

### Integration with Packets

```python
# Create configuration
config = FieldConfig.create_standard(addr_width=32, data_width=32)

# Create packet using configuration
packet = config.create_packet()

# Set field values
packet.addr = 0x12345678
packet.data = 0xDEADBEEF

# Access field configuration
addr_field = config.get_field("addr")
print(f"Address field: {addr_field.bits} bits, format: {addr_field.format}")
```

### Rich Table Display

```python
# Display configuration in formatted table
print(config.debug_str())

# Output:
# ┏━━━━━━━━━━━━┳━━━━━━┳━━━━━━━━┳━━━━━━━━━━━━━┳━━━━━━━━━┳━━━━━━━━━━┳━━━━━━━━━━━━━━━━━━━━┓
# ┃ Field Name ┃ Bits ┃ Format ┃ Active Bits ┃ Default ┃ Encoding ┃ Description        ┃
# ┡━━━━━━━━━━━━╇━━━━━━╇━━━━━━━━╇━━━━━━━━━━━━━╇━━━━━━━━━╇━━━━━━━━━━╇━━━━━━━━━━━━━━━━━━━━┩
# │ addr       │   32 │ hex    │ (31:0)      │     0x0 │          │ Address            │
# │ data       │   32 │ hex    │ (31:0)      │     0x0 │          │ Data value         │
# └────────────┴──────┴────────┴─────────────┴─────────┴──────────┴────────────────────┘
# Total bits: 64
```

### Converting Legacy Configurations

```python
# Legacy dictionary format
legacy_config = {
    'addr': {
        'bits': 32,
        'format': 'hex',
        'default': 0,
        'description': 'Address field'
    },
    'data': {
        'bits': 32, 
        'format': 'hex',
        'default': 0,
        'description': 'Data field'
    }
}

# Convert to new format
modern_config = FieldConfig.from_dict(legacy_config)

# Or with validation
validated_config = FieldConfig.validate_and_create(legacy_config)
```

## Error Handling

The FieldConfig system includes comprehensive error handling:

### Field Definition Validation
- **Bit Width**: Must be positive integer
- **Active Bits**: Must be within field bounds
- **Format**: Must be 'hex', 'bin', or 'dec'
- **Encoding**: Keys must be integers, values must be strings

### Configuration Validation
- **Duplicate Fields**: Prevents adding fields with same name
- **Missing Fields**: Graceful handling of missing field lookups
- **Type Checking**: Ensures proper types for all parameters

### Error Messages
```python
try:
    config.add_field(FieldDefinition("test", bits=-5))
except ValueError as e:
    # Error: Invalid active_bits (4:-1) for field 'test' with width -5
    pass

try:
    config.get_field("nonexistent")
except KeyError as e:
    # Error: Field 'nonexistent' not found in configuration
    pass
```

## Best Practices

1. **Use Method Chaining**: Take advantage of fluent interface for building configurations
2. **Validate Early**: Use `validate_and_create()` for external configurations
3. **Document Fields**: Always provide meaningful descriptions
4. **Use Encoding**: Define state names for control fields
5. **Check Existence**: Use `has_field()` before accessing optional fields
6. **Display Configs**: Use `debug_str()` for configuration review and documentation

## Integration with Other Components

FieldConfig integrates seamlessly with other framework components:

- **Packet**: Provides field structure and validation
- **PacketFactory**: Uses FieldConfig for packet creation
- **DataStrategies**: Uses field information for efficient collection/driving
- **FlexRandomizer**: Can generate values based on field bit widths
- **Memory Model**: Uses field definitions for transaction processing
