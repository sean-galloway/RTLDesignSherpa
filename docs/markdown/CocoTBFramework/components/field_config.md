# Field Configuration Documentation

## Overview
The Field Configuration module provides robust classes for defining and managing field configurations in digital protocol verification. It includes:

1. `FieldDefinition`: Defines individual fields with type safety and validation
2. `FieldConfig`: Manages collections of fields with ordering and validation

This module replaces the older dictionary-based approach with proper class structures, providing better type safety, validation, and maintainability.

## FieldDefinition Class

### Purpose
The `FieldDefinition` class provides a robust, type-safe way to define a single field within a packet, with validation and automatic derivation of related properties.

### Class Definition
```python
@dataclass
class FieldDefinition:
    """
    Definition of a single field within a packet.
    
    Attributes:
        name: Field name
        bits: Width of the field in bits
        default: Default value for the field
        format: Display format ('hex', 'bin', 'dec')
        display_width: Width for display formatting
        active_bits: Tuple of (msb, lsb) defining active bit range
        description: Human-readable description of the field
    """
    name: str
    bits: int
    default: int = 0
    format: str = "hex"
    display_width: int = 0
    active_bits: Optional[Tuple[int, int]] = None
    description: Optional[str] = None
```

### Key Features

#### Post-Initialization Validation
```python
def __post_init__(self):
    """Validate and set derived values after initialization"""
```
Performs automatic validation and sets derived values:
- Sets `active_bits` to full width if not specified
- Validates `active_bits` range against field width
- Calculates appropriate `display_width` based on format
- Sets default `description` based on field name

#### Conversion Methods
```python
def to_dict(self) -> Dict[str, Any]:
    """Convert to dictionary format for backward compatibility"""
```
Converts the field definition to a dictionary for backward compatibility.

```python
@classmethod
def from_dict(cls, name: str, field_dict: Dict[str, Any]) -> 'FieldDefinition':
    """Create a FieldDefinition from a dictionary representation"""
```
Creates a field definition from a dictionary representation.

## FieldConfig Class

### Purpose
The `FieldConfig` class manages a collection of field definitions, maintaining field order and providing helper methods for field manipulation.

### Class Definition
```python
class FieldConfig:
    """
    Configuration of all fields in a packet, maintaining field order and providing
    helper methods for field manipulation.
    
    This class replaces the dictionary-based approach with a more robust structure
    that maintains field order and provides validation.
    """
```

### Key Features

#### Field Management
```python
def add_field(self, field_def: FieldDefinition) -> 'FieldConfig':
    """
    Add a field to the configuration.
    """
```
Adds a field to the configuration, maintaining order.

```python
def add_field_dict(self, name: str, field_dict: Dict[str, Any]) -> 'FieldConfig':
    """
    Add a field from dictionary representation (for backward compatibility).
    """
```
Adds a field from a dictionary representation for backward compatibility.

```python
def remove_field(self, name: str) -> 'FieldConfig':
    """
    Remove a field from the configuration.
    """
```
Removes a field from the configuration.

#### Field Access
```python
def get_field(self, name: str) -> FieldDefinition:
    """
    Get a field definition by name.
    """
```
Gets a field definition by name.

```python
def has_field(self, name: str) -> bool:
    """
    Check if a field exists in the configuration.
    """
```
Checks if a field exists in the configuration.

```python
def field_names(self) -> List[str]:
    """
    Get ordered list of field names.
    """
```
Gets an ordered list of field names.

```python
def fields(self) -> List[FieldDefinition]:
    """
    Get ordered list of field definitions.
    """
```
Gets an ordered list of field definitions.

#### Dictionary-Like Interface
The class provides dictionary-like access methods:
```python
def items(self):
    """Get name/definition pairs in order, similar to dict.items()."""
```

```python
def __iter__(self):
    """Iterator over field names (like dict.__iter__)"""
```

```python
def __getitem__(self, name: str) -> FieldDefinition:
    """Dict-like access to fields"""
```

```python
def __contains__(self, name: str) -> bool:
    """Support for 'in' operator"""
```

```python
def __len__(self) -> int:
    """Number of fields in the configuration"""
```

#### Conversion Methods
```python
def to_dict(self) -> Dict[str, Dict[str, Any]]:
    """
    Convert to dictionary format for backward compatibility.
    """
```
Converts the field configuration to a dictionary for backward compatibility.

```python
@classmethod
def from_dict(cls, field_dict: Dict[str, Dict[str, Any]]) -> 'FieldConfig':
    """
    Create a FieldConfig from a dictionary representation.
    """
```
Creates a field configuration from a dictionary representation.

#### Field Modification
```python
def update_field_width(self, field_name: str, new_bits: int, update_active_bits: bool = True) -> 'FieldConfig':
    """
    Update a field's bit width and optionally its active bits.
    """
```
Updates a field's bit width and optionally its active bits.

#### Validation and Creation
```python
@classmethod
def validate_and_create(cls, field_dict: Dict[str, Dict[str, Any]], raise_errors: bool = False) -> 'FieldConfig':
    """
    Validate a dictionary-based field configuration and convert to FieldConfig object.
    """
```
Validates a dictionary-based field configuration and converts it to a `FieldConfig` object.

#### Factory Methods
```python
@classmethod
def create_data_only(cls, data_width: int = 32) -> 'FieldConfig':
    """
    Create a simple data-only field configuration.
    """
```
Creates a simple field configuration with only a data field.

```python
@classmethod
def create_standard(cls, addr_width: int = 32, data_width: int = 32) -> 'FieldConfig':
    """
    Create a standard address/data field configuration.
    """
```
Creates a standard field configuration with address and data fields.

```python
@classmethod
def create_multi_data(cls, addr_width: int = 4, ctrl_width: int = 4, 
                        data_width: int = 8, num_data: int = 2) -> 'FieldConfig':
    """
    Create a multi-data field configuration with addr, ctrl, and multiple data fields.
    """
```
Creates a field configuration with address, control, and multiple data fields.

#### Utilities
```python
def get_total_bits(self) -> int:
    """
    Calculate the total number of bits across all fields.
    """
```
Calculates the total number of bits across all fields.

```python
def debug_str(self, indent=0) -> str:
    """
    Return a formatted string representation of the field configuration using Rich.
    """
```
Returns a formatted string representation of the field configuration.

## Usage Examples

### Creating Field Definitions
```python
# Create a simple field definition
addr_field = FieldDefinition(
    name="addr",
    bits=32,
    format="hex",
    description="Address field"
)

# Create a field with active bits specification
data_field = FieldDefinition(
    name="data",
    bits=32,
    default=0,
    format="hex",
    active_bits=(31, 2),  # Only bits 31:2 are active
    description="Data field"
)

# Create a control field
ctrl_field = FieldDefinition(
    name="ctrl",
    bits=4,
    default=0,
    format="bin",
    description="Control field"
)
```

### Building a Field Configuration
```python
# Create an empty configuration
config = FieldConfig()

# Add fields
config.add_field(addr_field)
config.add_field(data_field)
config.add_field(ctrl_field)

# Access fields
addr_def = config.get_field("addr")
print(f"Address field width: {addr_def.bits} bits")

# Check if field exists
if config.has_field("data"):
    print("Data field exists")

# Field names in order
field_names = config.field_names()
print(f"Fields in order: {field_names}")

# Total bits
total_bits = config.get_total_bits()
print(f"Total bits: {total_bits}")
```

### Using Factory Methods
```python
# Create standard address/data configuration
std_config = FieldConfig.create_standard(addr_width=32, data_width=64)
print(std_config.debug_str())

# Create data-only configuration
data_config = FieldConfig.create_data_only(data_width=128)
print(data_config.debug_str())

# Create multi-data configuration
multi_config = FieldConfig.create_multi_data(
    addr_width=8,
    ctrl_width=4,
    data_width=32,
    num_data=4  # Creates data0, data1, data2, data3
)
print(multi_config.debug_str())
```

### Dictionary Conversion
```python
# Convert to dictionary for backward compatibility
config_dict = config.to_dict()

# Create from dictionary
new_config = FieldConfig.from_dict(config_dict)

# Validate and create from dictionary
field_dict = {
    'addr': {
        'bits': 32,
        'format': 'hex'
    },
    'data': {
        'bits': 64,
        'format': 'hex'
    }
}
validated_config = FieldConfig.validate_and_create(field_dict)
```

### Updating Field Properties
```python
# Update a field's width
config.update_field_width("data", 64)

# Update without changing active bits
config.update_field_width("addr", 64, update_active_bits=False)
```

## Best Practices

1. **Use Factory Methods**: Use the factory methods like `create_standard()` when creating common configurations.

2. **Validate Dictionary Configs**: When using dictionary-based configurations, use `validate_and_create()` to ensure the configuration is valid.

3. **Set Appropriate Display Formats**: Choose the right format for each field type:
   - Use `hex` for addresses and most data fields
   - Use `bin` for control fields with bit-wise meaning
   - Use `dec` for counts and small numeric values

4. **Use Active Bits**: Specify `active_bits` when not all bits in a field are used.

5. **Provide Descriptions**: Add clear descriptions for each field to improve readability and documentation.

6. **Consistent Ordering**: Maintain consistent field ordering between related protocols to simplify protocol transformations.

7. **Field Naming Conventions**: Use consistent field naming conventions for related protocols.

8. **Integration with Packet Classes**: Use the field configuration with packet classes for complete protocol verification:
   ```python
   # Create field configuration
   field_config = FieldConfig.create_standard()
   
   # Create packet with this configuration
   packet = Packet(field_config, addr=0x1000, data=0xABCD)
   ```
