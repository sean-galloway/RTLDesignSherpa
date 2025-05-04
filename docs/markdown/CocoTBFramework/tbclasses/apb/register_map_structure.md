# Register Map Data Structure

This document explains the structure of the register definition files used by the `RegisterMap` class. These files define the hardware registers for verification and testing.

## Overview

The register map data structure is a hierarchical Python dictionary that describes a complete set of hardware registers, their fields, and properties. This structure is typically defined in a Python file that is imported by the `RegisterMap` class.

## Top-Level Structure

The top-level structure is a dictionary with a single key-value pair:

```python
top_block = {
    'block_name': {
        # Block contents
    }
}
```

Where:
- `top_block` is the dictionary variable exported by the module
- `'block_name'` is a string identifier for the register block
- The nested dictionary contains all block contents

## Block Structure

The block defines the overall register space:

```python
'block_name': {
    'type': 'block',
    'sid': "x:y",                    # Structure identifier
    'name': "block_name",            # Block name
    'offset': "0",                   # Base offset (hex string)
    'max_reg_size': "32",            # Maximum register size in bits
    'address': "0x000",              # Start address (hex string)
    'endaddress': "0x4FF",           # End address (hex string)
    'size': "1280",                  # Block size in bytes
    'config': {                      # Block configuration
        # Configuration details
    },
    # Register definitions follow
    'register1': {
        # Register 1 definition
    },
    'register2': {
        # Register 2 definition
    }
    # Additional registers...
}
```

## Configuration Structure

The `config` section defines global properties for the block:

```python
'config': {
    'type': 'config',
    'regwidth': "32",                # Default register width
    'chipbits': "0",                 # Chip select bits
    'blockbits': "0",                # Block select bits
    'regbits': "0",                  # Register select bits
    'addressunit': "8",              # Address unit (bits)
    'buswidth': "32",                # Bus width (bits)
    'busdomains': {                  # Bus domains
        # Bus domain definitions
    },
    'variants': {                    # Block variants
        # Variant definitions
    }
}
```

## Register Structure

Each register is defined as a key-value pair:

```python
'register_name': {
    'type': 'reg',
    'sid': "x:y",                    # Structure identifier
    'name': "register_name",         # Register name
    'offset': "offset_value",        # Offset from block base (decimal)
    'reset_type': "async",           # Reset type
    'address': "0x100",              # Register address (hex string)
    'endaddress': "0x103",           # End address for multi-byte regs (hex)
    'size': "4",                     # Register size in bytes
    'default': "0x00000000",         # Default/reset value (hex string)
    'sw': "rw",                      # Software access (rw, wo, ro, etc.)
    'hw': "ro",                      # Hardware access (ro, wo, rw, etc.)
    'count': "4",                    # Number of instances (if array)
    'config': {                      # Register-specific config
        # Configuration details
    },
    # Field definitions follow
    'field1': {
        # Field 1 definition
    },
    'field2': {
        # Field 2 definition
    }
    # Additional fields...
}
```

Common software access types:
- `rw` - Read/Write
- `ro` - Read Only
- `wo` - Write Only
- `r/w1c` - Read/Write 1 to Clear
- `r/w1s` - Read/Write 1 to Set

## Field Structure

Each field within a register is defined as:

```python
'field_name': {
    'type': 'field',
    'sid': "x:y",                    # Structure identifier
    'name': "field_name",            # Field name
    'offset': "31:0",                # Bit position (high:low or single bit)
    'default': "0x0",                # Default value (hex string)
    'sw': "rw",                      # Software access (rw, wo, ro, etc.)
    'hw': "ro",                      # Hardware access (ro, wo, rw, etc.)
    'doc': "Field description"       # Optional documentation
}
```

For the `offset` field:
- For a single bit: `"0"` (bit 0)
- For a bit range: `"15:0"` (bits 0 through 15)

## Bus Domain Structure

The bus domains section defines information about bus interfaces:

```python
'busdomains': {
    'default_map': {
        'type': 'busdomain',
        'name': "default_map",
        'bus': "APB",                # Bus type 
        'addressUnit': "8",          # Address unit (bits)
        'offset': "0",               # Offset within block
        'address': "0x000",          # Start address (hex string)
        'endaddress': "0x4FF",       # End address (hex string)
        'size': "1280"               # Size in bytes
    }
}
```

## Variant Structure

Variants define different versions of the register block:

```python
'variants': {
    'none': {
        'type': 'variant',
        'name': "none",
        'isselected': "true",
        'doc': "Variant description"
    }
}
```

## Example Flow

To understand how these structures relate:

1. Each register block contains multiple registers
2. Each register contains multiple fields
3. Fields are the smallest addressable units with specific bit positions
4. Bus domains define how the register space is accessed

## Usage by RegisterMap

The `RegisterMap` class:

1. Loads this structure from a Python file
2. Processes it to extract register information
3. Creates a flattened representation of registers and fields
4. Provides methods to access and modify register values
5. Generates APB transactions to access the hardware registers

## Key Characteristics

1. **Text-Based Values**: Most numeric values are stored as hex or decimal strings
2. **Hierarchical Structure**: Blocks contain registers which contain fields
3. **Access Controls**: Fields specify software and hardware access permissions
4. **Metadata**: Additional information like documentation is included
5. **Addressing**: Detailed addressing information for precise memory mapping
