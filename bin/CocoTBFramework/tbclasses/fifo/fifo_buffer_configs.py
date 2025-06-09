"""Shared Field Configurations for FIFO Buffer Tests

Simplified to only contain field configurations. Randomization is now handled
by FlexConfigGen in the individual testbenches.
"""

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

    # Field mode - addr, ctrl, data0, data1 fields
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
