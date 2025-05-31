# This is the corrected version with all [min, max] changed to (min, max)
RANDOMIZER_CONFIGS = {
    'fixed': {
        'write': {
            'valid_delay': ([(2, 2)], [1])
        },
        'read': {
            'ready_delay': ([(2, 2)], [1])
        }
    },
    'constrained': {
        'write': {
            'valid_delay': ([(0, 0), (1, 8), (9, 20)], [5, 2, 1])
        },
        'read': {
            'ready_delay': ([(0, 1), (2, 8), (9, 30)], [5, 2, 1])
        }
    },
    'fast': {
        'write': {
            'valid_delay': ([(0, 0), (1, 8), (9, 20)], [5, 0, 0])
        },
        'read': {
            'ready_delay': ([(0, 0), (1, 8), (9, 30)], [5, 0, 0])
        }
    },
    'backtoback': {
        'write': {
            'valid_delay': ([(0, 0)], [1])
        },
        'read': {
            'ready_delay': ([(0, 0)], [1])
        }
    },
    'burst_pause': {
        'write': {
            'valid_delay': ([(0, 0), (15, 25)], [10, 1])
        },
        'read': {
            'ready_delay': ([(0, 0), (1, 5)], [10, 1])
        }
    },
    'slow_consumer': {
        'write': {
            'valid_delay': ([(0, 0)], [1])
        },
        'read': {
            'ready_delay': ([(10, 20)], [1])
        }
    },
    'slow_producer': {
        'write': {
            'valid_delay': ([(10, 20)], [1])
        },
        'read': {
            'ready_delay': ([(0, 0)], [1])
        }
    }
}
