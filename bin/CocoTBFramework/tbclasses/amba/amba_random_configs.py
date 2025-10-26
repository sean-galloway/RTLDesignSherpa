# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: amba_random_configs
# Purpose: Amba Random Configs implementation
#
# Documentation: bin/CocoTBFramework/README.md
# Subsystem: framework
#
# Author: sean galloway
# Created: 2025-10-18

APB_MASTER_RANDOMIZER_CONFIGS = {
    'fixed': {
        'psel': ([(1, 1)], [1]),
        'penable': ([(1, 1)], [1])
    },
    'constrained': {
        'psel': ([(0, 0), (1, 5), (6, 10)], [5, 3, 1]),
        'penable': ([(0, 0), (1, 3)], [3, 1])
    },
    'fast': {
        'psel': ([(0, 0), (1, 5), (6, 10)], [5, 0, 0]),
        'penable': ([(0, 0), (1, 3)], [3, 0])
    },
    'backtoback': {
        'psel': ([(0, 0)], [1]),
        'penable': ([(0, 0)], [1])
    },
    'burst_pause': {
        'psel': ([(0, 0), (5, 10)], [8, 1]),
        'penable': ([(0, 0), (2, 5)], [8, 1])
    },
    'slow_master': {
        'psel': ([(5, 15)], [1]),
        'penable': ([(3, 8)], [1])
    }
}

# APB Slave Randomizer Configurations
APB_SLAVE_RANDOMIZER_CONFIGS = {
    'fixed': {
        'ready': ([(1, 1)], [1]),
        'error': ([(0, 0)], [1])
    },
    'constrained': {
        'ready': ([(0, 0), (1, 5), (6, 10)], [5, 3, 1]),
        'error': ([(0, 0), (1, 1)], [10, 0])
    },
    'fast': {
        'ready': ([(0, 0), (1, 5), (6, 10)], [5, 0, 0]),
        'error': ([(0, 0)], [1])
    },
    'backtoback': {
        'ready': ([(0, 0)], [1]),
        'error': ([(0, 0)], [1])
    },
    'burst_pause': {
        'ready': ([(0, 0), (8, 15)], [8, 1]),
        'error': ([(0, 0)], [1])
    },
    'slow_consumer': {
        'ready': ([(8, 20)], [1]),
        'error': ([(0, 0)], [1])
    },
    'error_injection': {
        'ready': ([(0, 2)], [1]),
        'error': ([(0, 0), (1, 1)], [8, 2])
    }
}

# AXI Randomizer Configurations
AXI_RANDOMIZER_CONFIGS = {
    'fixed': {
        'master': {
            'valid_delay': ([(1, 1)], [1])
        },
        'slave': {
            'ready_delay': ([(1, 1)], [1])
        }
    },
    'constrained': {
        'master': {
            'valid_delay': ([(0, 0), (1, 5), (6, 10)], [5, 3, 1])
        },
        'slave': {
            'ready_delay': ([(0, 0), (1, 5), (6, 10)], [5, 3, 1])
        }
    },
    'fast': {
        'master': {
            'valid_delay': ([(0, 0), (1, 5), (6, 10)], [5, 0, 0])
        },
        'slave': {
            'ready_delay': ([(0, 0), (1, 5), (6, 10)], [5, 0, 0])
        }
    },
    'backtoback': {
        'master': {
            'valid_delay': ([(0, 0)], [1])
        },
        'slave': {
            'ready_delay': ([(0, 0)], [1])
        }
    },
    'burst_pause': {
        'master': {
            'valid_delay': ([(0, 0), (10, 20)], [8, 1])
        },
        'slave': {
            'ready_delay': ([(0, 0), (12, 25)], [8, 1])
        }
    },
    'slow_producer': {
        'master': {
            'valid_delay': ([(8, 20)], [1])
        },
        'slave': {
            'ready_delay': ([(8, 20)], [1])
        }
    },
    'high_throughput': {
        'master': {
            'valid_delay': ([(0, 1)], [1])
        },
        'slave': {
            'ready_delay': ([(0, 1)], [1])
        }
    }
}
