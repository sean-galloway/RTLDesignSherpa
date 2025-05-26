# FIFO Buffer Configs

## Overview

The `fifo_buffer_configs` module provides shared configuration definitions for FIFO testbenches. It defines field configurations for different FIFO data structures and randomization profiles for controlling timing behavior. These configurations are used across the various FIFO testbench classes to ensure consistent behavior and simplified test configuration.

## Module Definition

```python
'''Shared Configs for the GAXI Buffer tests'''

# Field configurations for different test modes
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
    # Additional randomizer configurations...
}
```

## Key Features

- Standardized field configurations for different FIFO data formats
- Consistent randomization patterns for timing control
- Support for single-field and multi-field data structures
- Various delay profiles for realistic testing scenarios
- Configuration sharing across all FIFO testbenches

## Field Configurations

### Standard Configuration

Simple configuration with a single data field for basic FIFOs:

```python
'standard': {
    'data': {
        'bits': 32,  # Will be updated based on config
        'default': 0,
        'format': 'hex',
        'display_width': 8,
        'active_bits': (31, 0),  # Will be updated based on config
        'description': 'Data value'
    }
}
```

### Field Configuration

Multi-field configuration for more complex FIFOs:

```python
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
```

## Randomization Configurations

The module defines several randomization profiles for timing control:

### Fixed

Fixed delay of 2 cycles for both read and write operations:

```python
'fixed': {
    'write': {
        'valid_delay': ([[2, 2]], [1])
    },
    'read': {
        'ready_delay': ([[2, 2]], [1])
    }
}
```

### Constrained

Realistic mixture of delays with weighted distribution:

```python
'constrained': {
    'write': {
        'valid_delay': ([[0, 0], [1, 8], [9, 20]], [5, 2, 1])
    },
    'read': {
        'ready_delay': ([[0, 1], [2, 8], [9, 30]], [5, 2, 1])
    }
}
```

This creates a distribution where:
- 62.5% of delays are 0 cycles (5/8 weight)
- 25% of delays are between 1-8 cycles (2/8 weight)
- 12.5% of delays are between 9-20 cycles (1/8 weight)

### Fast

Optimized for high-throughput testing with minimal delays:

```python
'fast': {
    'write': {
        'valid_delay': ([[0, 0], [1, 8], [9, 20]], [5, 0, 0])
    },
    'read': {
        'ready_delay': ([[0, 0], [1, 8], [9, 30]], [5, 0, 0])
    }
}
```

### Back-to-Back

No delays between transfers for maximum throughput:

```python
'backtoback': {
    'write': {
        'valid_delay': ([[0, 0]], [1])
    },
    'read': {
        'ready_delay': ([[0, 0]], [1])
    }
}
```

### Burst/Pause

Bursts of transfers followed by pauses:

```python
'burst_pause': {
    'write': {
        'valid_delay': ([[0, 0], [15, 25]], [10, 1])
    },
    'read': {
        'ready_delay': ([[0, 0], [1, 5]], [10, 1])
    }
}
```

### Slow Consumer

Fast producer with slow consumer for backpressure testing:

```python
'slow_consumer': {
    'write': {
        'valid_delay': ([[0, 0]], [1])
    },
    'read': {
        'ready_delay': ([[10, 20]], [1])
    }
}
```

### Slow Producer

Slow producer with fast consumer:

```python
'slow_producer': {
    'write': {
        'valid_delay': ([[10, 20]], [1])
    },
    'read': {
        'ready_delay': ([[0, 0]], [1])
    }
}
```

## Usage Examples

Field configuration usage:

```python
from CocoTBFramework.tbclasses.fifo.fifo_buffer_configs import FIELD_CONFIGS
from CocoTBFramework.components.field_config import FieldConfig

# Create field configuration
field_config = FieldConfig.from_dict(FIELD_CONFIGS['standard'])
field_config.update_field_width('data', data_width)

# Create multi-field configuration
field_config = FieldConfig.from_dict(FIELD_CONFIGS['field'])
field_config.update_field_width('addr', addr_width)
field_config.update_field_width('ctrl', ctrl_width)
field_config.update_field_width('data0', data_width)
field_config.update_field_width('data1', data_width)
```

Randomizer configuration usage:

```python
from CocoTBFramework.tbclasses.fifo.fifo_buffer_configs import RANDOMIZER_CONFIGS
from CocoTBFramework.components.flex_randomizer import FlexRandomizer

# Set randomizers for master and slave
master.set_randomizer(FlexRandomizer(RANDOMIZER_CONFIGS['constrained']['write']))
slave.set_randomizer(FlexRandomizer(RANDOMIZER_CONFIGS['constrained']['read']))

# Use different profiles for different test phases
# Fast for basic functionality
master.set_randomizer(FlexRandomizer(RANDOMIZER_CONFIGS['fast']['write']))
slave.set_randomizer(FlexRandomizer(RANDOMIZER_CONFIGS['fast']['read']))

# Slow consumer for backpressure testing
master.set_randomizer(FlexRandomizer(RANDOMIZER_CONFIGS['backtoback']['write']))
slave.set_randomizer(FlexRandomizer(RANDOMIZER_CONFIGS['slow_consumer']['read']))
```

## Implementation Notes

- Field configurations define the structure of FIFO packets
- Field definitions include bit width, default value, and formatting information
- Field widths are updated based on test parameters
- Randomizer configurations define timing behavior using FlexRandomizer format
- Each randomizer profile has a specific testing purpose
- Configurations are shared across all FIFO testbenches for consistency

## Field Definition Requirements

Each field definition includes:

- **bits**: Width of the field in bits
- **default**: Default value when not explicitly set
- **format**: Display format ('hex', 'dec', etc.)
- **display_width**: Number of characters for formatted display
- **active_bits**: Range of active bits in the field
- **description**: Description of the field purpose

## See Also

- [FIFO Buffer](fifo_buffer.md) - Standard FIFO testbench
- [FIFO Buffer Field](fifo_buffer_field.md) - Field-based FIFO testbench
- [Field Config](../../components/field_config.md) - Field configuration component
- [Flex Randomizer](../../components/flex_randomizer.md) - Randomization component

## Navigation

[↑ FIFO Testbenches Index](index.md) | [↑ TBClasses Index](../index.md) | [↑ CocoTBFramework Index](../../index.md)
