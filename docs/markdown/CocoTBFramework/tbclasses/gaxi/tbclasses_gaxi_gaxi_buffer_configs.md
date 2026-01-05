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

# gaxi_buffer_configs.py

Shared field configurations for GAXI buffer tests. This module provides standardized field definitions that ensure consistency across all GAXI testbench components while supporting flexible bit width configuration.

## Overview

The `gaxi_buffer_configs.py` module contains the `FIELD_CONFIGS` dictionary that defines field structures for different GAXI testing modes. The configuration system has been simplified to focus purely on field definitions, with randomization now handled by FlexConfigGen in individual testbenches.

### Key Features
- **Standardized field definitions** across all GAXI testbenches
- **Dynamic bit width configuration** based on test parameters
- **Two primary modes**: 'standard' and 'field' testing
- **Consistent field properties** (format, display, description)
- **Runtime bit width updates** for flexible testing

## Configuration Structure

### FIELD_CONFIGS Dictionary

```python
FIELD_CONFIGS = {
    'standard': { ... },  # Single data field configuration
    'field': { ... }      # Multi-field configuration
}
```

## Standard Mode Configuration

Used by `GaxiBufferTB` for basic single-field testing:

```python
'standard': {
    'data': {
        'bits': 32,                    # Default width, updated at runtime
        'default': 0,                  # Default field value
        'format': 'hex',               # Display format (hex, dec, bin)
        'display_width': 8,            # Display width in characters
        'active_bits': (31, 0),        # Active bit range (MSB, LSB)
        'description': 'Data value'    # Human-readable description
    }
}
```

### Standard Mode Usage

The standard mode is designed for simple buffer testing with a single data field:

**Characteristics**:
- Single `data` field contains all information
- Configurable width based on `TEST_DATA_WIDTH`
- Suitable for basic FIFO and skid buffer testing
- Minimal overhead for simple test scenarios

**Runtime Configuration**:
```python
# Bit width updated based on environment variable
config = FIELD_CONFIGS['standard'].copy()
config['data']['bits'] = int(os.environ.get('TEST_DATA_WIDTH', '32'))
config['data']['active_bits'] = (config['data']['bits']-1, 0)
```

## Field Mode Configuration

Used by `GaxiFieldBufferTB` and multi-field testbenches:

```python
'field': {
    'addr': {
        'bits': 32,                      # Address field width
        'default': 0,                    # Default address value
        'format': 'hex',                 # Hexadecimal display
        'display_width': 2,              # Compact address display
        'active_bits': (31, 0),          # Full address range
        'description': 'Address value'   # Field description
    },
    'ctrl': {
        'bits': 8,                       # Control field width
        'default': 0,                    # Default control value
        'format': 'hex',                 # Hexadecimal display
        'display_width': 2,              # Control display width
        'active_bits': (7, 0),           # Control bit range
        'description': 'Control value'   # Field description
    },
    'data0': {
        'bits': 32,                      # Data0 field width
        'default': 0,                    # Default data value
        'format': 'hex',                 # Hexadecimal display
        'display_width': 4,              # Data display width
        'active_bits': (31, 0),          # Data bit range
        'description': 'Data0 value'     # Field description
    },
    'data1': {
        'bits': 32,                      # Data1 field width
        'default': 0,                    # Default data value
        'format': 'hex',                 # Hexadecimal display
        'display_width': 4,              # Data display width
        'active_bits': (31, 0),          # Data bit range
        'description': 'Data1 value'     # Field description
    }
}
```

### Field Mode Usage

The field mode enables sophisticated multi-field testing scenarios:

**Field Purpose**:
- `addr`: Address or identifier field
- `ctrl`: Control or command field
- `data0`: Primary data payload
- `data1`: Secondary data payload

**Characteristics**:
- Independent width configuration for each field
- Separate validation and randomization per field
- Support for complex packet structures
- Suitable for advanced protocol testing

## Field Properties

### Core Properties

Each field definition includes the following properties:

**bits**: Field width in bits
- Determines the valid value range (0 to 2^bits - 1)
- Updated at runtime based on environment variables
- Affects display formatting and validation

**default**: Default field value
- Used for field initialization
- Fallback value for undefined cases
- Starting point for randomization ranges

**format**: Display format specification
- `'hex'`: Hexadecimal display (most common)
- `'dec'`: Decimal display
- `'bin'`: Binary display
- Affects logging and debug output

**display_width**: Character width for display
- Controls field formatting in logs and reports
- Ensures consistent alignment in output
- Calculated based on field width and format

**active_bits**: Bit range specification
- Tuple of (MSB, LSB) indices
- Defines which bits are meaningful
- Used for validation and constraint generation

**description**: Human-readable field description
- Documentation for field purpose
- Used in error messages and reports
- Helps with debug and analysis

## Runtime Configuration

### Dynamic Width Updates

Field configurations are updated at runtime based on environment variables:

```python
# Environment variable mapping
ENV_MAPPING = {
    'addr': 'TEST_ADDR_WIDTH',
    'ctrl': 'TEST_CTRL_WIDTH', 
    'data': 'TEST_DATA_WIDTH',
    'data0': 'TEST_DATA_WIDTH',
    'data1': 'TEST_DATA_WIDTH'
}

# Update field widths
def update_field_config(config, field_name, width):
    if field_name in config:
        config[field_name]['bits'] = width
        config[field_name]['active_bits'] = (width-1, 0)
        # Update display width based on format
        if config[field_name]['format'] == 'hex':
            config[field_name]['display_width'] = (width + 3) // 4
```

### FieldConfig Integration

The configurations integrate seamlessly with the FieldConfig system:

```python
from CocoTBFramework.components.shared.field_config import FieldConfig, FieldDefinition

# Create FieldConfig from FIELD_CONFIGS
def create_field_config(mode='field'):
    base_config = FIELD_CONFIGS[mode]
    field_config = FieldConfig()
    
    for field_name, field_props in base_config.items():
        field_def = FieldDefinition(
            name=field_name,
            bits=field_props['bits'],
            default=field_props['default'],
            format=field_props['format'],
            display_width=field_props['display_width'],
            active_bits=field_props['active_bits'],
            description=field_props['description']
        )
        field_config.add_field(field_def)
    
    return field_config
```

## Usage Examples

### Basic Configuration Usage

```python
from CocoTBFramework.tbclasses.gaxi.gaxi_buffer_configs import FIELD_CONFIGS

# Get standard configuration
standard_config = FIELD_CONFIGS['standard']
print(f"Data field width: {standard_config['data']['bits']} bits")

# Get field configuration
field_config = FIELD_CONFIGS['field']
print(f"Address width: {field_config['addr']['bits']} bits")
print(f"Control width: {field_config['ctrl']['bits']} bits")
```

### Testbench Integration

```python
import os
from CocoTBFramework.tbclasses.gaxi.gaxi_buffer_configs import FIELD_CONFIGS

class GaxiFieldBufferTB(TBBase):
    def __init__(self, dut, **kwargs):
        super().__init__(dut, **kwargs)
        
        # Get environment parameters
        self.TEST_ADDR_WIDTH = int(os.environ.get('TEST_ADDR_WIDTH', '16'))
        self.TEST_CTRL_WIDTH = int(os.environ.get('TEST_CTRL_WIDTH', '8'))
        self.TEST_DATA_WIDTH = int(os.environ.get('TEST_DATA_WIDTH', '32'))
        
        # Create field configuration from base config
        base_config = FIELD_CONFIGS['field'].copy()
        
        # Update field widths
        base_config['addr']['bits'] = self.TEST_ADDR_WIDTH
        base_config['ctrl']['bits'] = self.TEST_CTRL_WIDTH
        base_config['data0']['bits'] = self.TEST_DATA_WIDTH
        base_config['data1']['bits'] = self.TEST_DATA_WIDTH
        
        # Update active bits ranges
        base_config['addr']['active_bits'] = (self.TEST_ADDR_WIDTH-1, 0)
        base_config['ctrl']['active_bits'] = (self.TEST_CTRL_WIDTH-1, 0)
        base_config['data0']['active_bits'] = (self.TEST_DATA_WIDTH-1, 0)
        base_config['data1']['active_bits'] = (self.TEST_DATA_WIDTH-1, 0)
        
        # Create FieldConfig object
        self.field_config = FieldConfig.validate_and_create(base_config)
```

### Custom Configuration Creation

```python
def create_custom_field_config(addr_width=16, ctrl_width=8, data_width=32):
    """Create custom field configuration with specified widths"""
    
    custom_config = {
        'addr': {
            'bits': addr_width,
            'default': 0,
            'format': 'hex',
            'display_width': (addr_width + 3) // 4,  # Hex digits needed
            'active_bits': (addr_width-1, 0),
            'description': f'Address field ({addr_width} bits)'
        },
        'ctrl': {
            'bits': ctrl_width,
            'default': 0,
            'format': 'hex',
            'display_width': (ctrl_width + 3) // 4,
            'active_bits': (ctrl_width-1, 0),
            'description': f'Control field ({ctrl_width} bits)'
        },
        'data': {
            'bits': data_width,
            'default': 0,
            'format': 'hex',
            'display_width': (data_width + 3) // 4,
            'active_bits': (data_width-1, 0),
            'description': f'Data field ({data_width} bits)'
        }
    }
    
    return custom_config
```

## Validation and Constraints

### Field Validation

Each field configuration includes validation constraints:

```python
def validate_field_config(config):
    """Validate field configuration consistency"""
    for field_name, field_props in config.items():
        # Check required properties
        required_props = ['bits', 'default', 'format', 'display_width', 'active_bits', 'description']
        for prop in required_props:
            if prop not in field_props:
                raise ValueError(f"Missing property '{prop}' in field '{field_name}'")
        
        # Validate bit ranges
        bits = field_props['bits']
        active_bits = field_props['active_bits']
        if active_bits[0] >= bits or active_bits[1] < 0:
            raise ValueError(f"Invalid active_bits {active_bits} for {bits}-bit field '{field_name}'")
        
        # Validate default value
        default_val = field_props['default']
        max_val = (1 << bits) - 1
        if default_val < 0 or default_val > max_val:
            raise ValueError(f"Default value {default_val} out of range for {bits}-bit field '{field_name}'")
```

### Configuration Constraints

**Width Constraints**:
- Minimum width: 1 bit
- Maximum width: 128 bits (practical limit)
- Address alignment considerations for addr field
- Control field typically 8-16 bits

**Value Constraints**:
- Default values must fit within field width
- Active bit ranges must be valid
- Display width should accommodate format requirements

## Best Practices

### Configuration Management

1. **Use Environment Variables**: Configure widths via environment variables for flexibility
2. **Validate Configurations**: Always validate configurations before use
3. **Document Changes**: Update descriptions when modifying field purposes
4. **Consistent Naming**: Use standard field names across testbenches

### Performance Considerations

1. **Cache Configurations**: Cache processed configurations to avoid repeated calculations
2. **Minimize Updates**: Update configurations once during initialization
3. **Efficient Display**: Choose appropriate display widths for performance
4. **Memory Usage**: Consider memory impact of large field widths

### Debugging Support

1. **Descriptive Names**: Use clear, descriptive field names
2. **Comprehensive Descriptions**: Include detailed field descriptions
3. **Consistent Formatting**: Use consistent display formats across related fields
4. **Error Context**: Provide field context in error messages

The `gaxi_buffer_configs.py` module provides a robust foundation for field configuration management across the GAXI testbench framework, ensuring consistency while maintaining flexibility for diverse testing scenarios.