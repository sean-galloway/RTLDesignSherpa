# GAXI Buffer Configurations

## Overview

The `gaxi_buffer_configs.py` module provides shared configuration definitions for GAXI buffer testbenches. It defines standardized field configurations for different types of GAXI interfaces and randomization configurations for controlling timing behavior during testing. These configurations are used across the GAXI testbench classes to ensure consistent operation and thorough verification.

## Configuration Components

### Field Configurations

The `FIELD_CONFIGS` dictionary defines the field structures for different types of GAXI interfaces:

```python
FIELD_CONFIGS = {
    # Standard mode - single data field
    'standard': {
        'data': {
            'bits': 32,  # Will be updated based on config
            'default': 0,
            'format': 'hex',
            'display_width': 8,
            'active_bits': (31, 0),  # Will be updated based on config
            'description': 'Data value'
        }
    },

    # field mode - addr, ctrl, data0, data1 fields
    'field': {
        'addr': {
            'bits': 32,  # Will be updated based on config
            'default': 0,
            'format': 'hex',
            'display_width': 2,
            'active_bits': (31, 0),  # Will be updated based on config
            'description': 'Address value'
        },
        'ctrl': {
            'bits': 8,  # Will be updated based on config
            'default': 0,
            'format': 'hex',
            'display_width': 2,
            'active_bits': (7, 0),  # Will be updated based on config
            'description': 'Control value'
        },
        'data0': {
            'bits': 32,  # Will be updated based on config
            'default': 0,
            'format': 'hex',
            'display_width': 4,
            'active_bits': (31, 0),  # Will be updated based on config
            'description': 'Data0 value'
        },
        'data1': {
            'bits': 32,  # Will be updated based on config
            'default': 0,
            'format': 'hex',
            'display_width': 4,
            'active_bits': (31, 0),  # Will be updated based on config
            'description': 'Data1 value'
        }
    }
}
```

### Randomization Configurations

The `RANDOMIZER_CONFIGS` dictionary defines various timing profiles for controlling signal timing during tests:

```python
RANDOMIZER_CONFIGS = {
    'fixed': {
        'write': {
            'valid_delay': ([[2, 2]], [1])
        },
        'read': {
            'ready_delay': ([[2, 2]], [1])
        }
    },
    'constrained': {
        'write': {
            'valid_delay': ([[0, 0], [1, 8], [9, 20]], [5, 2, 1])
        },
        'read': {
            'ready_delay': ([[0, 1], [2, 8], [9, 30]], [5, 2, 1])
        }
    },
    'fast': {
        'write': {
            'valid_delay': ([[0, 0], [1, 8], [9, 20]], [5, 0, 0])
        },
        'read': {
            'ready_delay': ([[0, 0], [1, 8], [9, 30]], [5, 0, 0])
        }
    },
    'backtoback': {
        'write': {
            'valid_delay': ([[0, 0]], [1])
        },
        'read': {
            'ready_delay': ([[0, 0]], [1])
        }
    },
    'burst_pause': {
        'write': {
            'valid_delay': ([[0, 0], [15, 25]], [10, 1])
        },
        'read': {
            'ready_delay': ([[0, 0], [1, 5]], [10, 1])
        }
    },
    'slow_consumer': {
        'write': {
            'valid_delay': ([[0, 0]], [1])
        },
        'read': {
            'ready_delay': ([[10, 20]], [1])
        }
    },
    'slow_producer': {
        'write': {
            'valid_delay': ([[10, 20]], [1])
        },
        'read': {
            'ready_delay': ([[0, 0]], [1])
        }
    }
}
```

## Field Configuration Details

### Standard Mode

The standard mode field configuration defines a single `data` field for simple data transfer:

- **data**: A configurable-width data field (default 32 bits)
  - Formatted as hexadecimal
  - Uses full bit range for active bits

### Field Mode

The field mode configuration defines a multi-field structure for more complex data transfer:

- **addr**: Address field (default 32 bits)
  - Used for addressing functionality
  - Formatted as hexadecimal
  
- **ctrl**: Control field (default 8 bits)
  - Used for control signals or flags
  - Formatted as hexadecimal
  
- **data0**: First data field (default 32 bits)
  - Primary data value
  - Formatted as hexadecimal
  
- **data1**: Second data field (default 32 bits)
  - Secondary data value
  - Formatted as hexadecimal

## Randomization Configuration Details

### Fixed Profile

- Fixed delay of 2 cycles for both valid and ready signals
- Provides deterministic timing behavior

### Constrained Profile

- Mix of zero, short, and medium delays with weighted distribution
- Write: 5:2:1 ratio for no delay, short delay (1-8 cycles), medium delay (9-20 cycles)
- Read: 5:2:1 ratio for minimal delay (0-1 cycles), short delay (2-8 cycles), medium delay (9-30 cycles)
- Provides realistic but controlled timing behavior

### Fast Profile

- Heavily weighted toward no delay for maximum throughput
- Removes medium delay options completely
- Useful for testing maximum throughput conditions

### Back-to-Back Profile

- Zero delay for both valid and ready signals
- Forces back-to-back transactions with no gaps
- Tests buffer's ability to handle continuous data flow

### Burst-Pause Profile

- Alternates between bursts of back-to-back transactions and pauses
- Write: 10:1 ratio for no delay versus long pauses (15-25 cycles)
- Read: 10:1 ratio for no delay versus short pauses (1-5 cycles)
- Tests buffer's behavior with bursty traffic patterns

### Slow Consumer Profile

- Fast producer (no delay on valid) but slow consumer (10-20 cycle delays on ready)
- Tests buffer's back-pressure handling and full buffer conditions
- Stresses flow control mechanisms

### Slow Producer Profile

- Slow producer (10-20 cycle delays on valid) but fast consumer (no delay on ready)
- Tests buffer's empty conditions and idle state behavior
- Checks for proper handling of sparse traffic

## Usage Examples

### Field Configuration Usage

```python
# Load standard configuration
self.field_config = FieldConfig.from_dict(FIELD_CONFIGS['standard'])

# Update field width based on test parameters
data_field = self.field_config.get_field('data')
data_field.active_bits = (self.DATA_WIDTH-1, 0)

# Load field mode configuration
self.field_config = FieldConfig.from_dict(FIELD_CONFIGS['field'])

# Update field widths
self.field_config.update_field_width('addr', self.AW)
self.field_config.update_field_width('ctrl', self.CW)
self.field_config.update_field_width('data0', self.DW)
self.field_config.update_field_width('data1', self.DW)
```

### Randomization Configuration Usage

```python
# Set up constrained randomizer for master
self.write_master.set_randomizer(
    FlexRandomizer(RANDOMIZER_CONFIGS['constrained']['write'])
)

# Set up back-to-back randomizer for slave
self.read_slave.set_randomizer(
    FlexRandomizer(RANDOMIZER_CONFIGS['backtoback']['read'])
)

# Switch to slow consumer profile
self.read_slave.set_randomizer(
    FlexRandomizer(RANDOMIZER_CONFIGS['slow_consumer']['read'])
)
```

## Implementation Notes

- Field configurations define the structure of data packets
- Width parameters are typically updated based on testbench configuration
- Randomization configurations control timing behavior
- Randomization parameters use weighted distributions for realistic behavior
- Each timing profile is optimized for testing specific aspects of the buffer

## See Also

- [GAXI Buffer](gaxi_buffer.md) - Basic GAXI buffer testbench
- [GAXI Buffer Field](gaxi_buffer_field.md) - Field-based GAXI testbench
- [GAXI Buffer Multi](gaxi_buffer_multi.md) - Multi-signal GAXI testbench
- [Field Config](../../components/field_config.md) - Field configuration details

## Navigation

[↑ GAXI Testbenches Index](index.md) | [↑ TBClasses Index](../index.md) | [↑ CocoTBFramework Index](../../index.md)
