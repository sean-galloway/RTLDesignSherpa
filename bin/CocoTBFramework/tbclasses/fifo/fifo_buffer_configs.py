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
            'write_delay': ([(2, 2)], [1])
        },
        'read': {
            'read_delay': ([(2, 2)], [1])
        }
    },
    'constrained': {
        'write': {
            'write_delay': ([(0, 0), (1, 8), (9, 20)], [5, 2, 1])
        },
        'read': {
            'read_delay': ([(0, 1), (2, 8), (9, 30)], [5, 2, 1])
        }
    },
    'fast': {
        'write': {
            'write_delay': ([(0, 0)], [1])  # Only use the fast bin
        },
        'read': {
            'read_delay': ([(0, 0)], [1])  # Only use the fast bin
        }
    },
    'backtoback': {
        'write': {
            'write_delay': ([(0, 0)], [1])
        },
        'read': {
            'read_delay': ([(0, 0)], [1])
        }
    },
    'burst_pause': {
        'write': {
            'write_delay': ([(0, 0), (15, 25)], [10, 1])
        },
        'read': {
            'read_delay': ([(0, 0), (1, 5)], [10, 1])
        }
    },
    'slow_consumer': {
        'write': {
            'write_delay': ([(0, 0)], [1])
        },
        'read': {
            'read_delay': ([(10, 20)], [1])
        }
    },
    'slow_producer': {
        'write': {
            'write_delay': ([(10, 20)], [1])
        },
        'read': {
            'read_delay': ([(0, 0)], [1])
        }
    }
}
