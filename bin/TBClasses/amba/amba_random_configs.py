# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: amba_random_configs
# Purpose: Amba Random Configs implementation
#
# Documentation: cocotb-framework PyPI package
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

# GAXI Randomizer Configurations
#
# Same nested shape as AXI_RANDOMIZER_CONFIGS so the application code is
# identical: a GAXI master consumes the 'master' section ('valid_delay') and a
# GAXI slave consumes the 'slave' section ('ready_delay'). GAXI BFMs call
# randomizer.next() each cycle and read 'valid_delay'/'ready_delay' (see
# GAXIMaster._xmit_phase1 / GAXISlave._recv_phase2).
#
# The first block mirrors the canonical AXI profiles so a profile name is valid
# on either interface family. The 'gaxi_*' block carries the GAXI-specific
# patterns proven in TBClasses/gaxi/gaxi_buffer.py (stress, backpressure, etc.),
# applied symmetrically to both valid_delay and ready_delay.
GAXI_RANDOMIZER_CONFIGS = {
    'fixed': {
        'master': {'valid_delay': ([(1, 1)], [1])},
        'slave':  {'ready_delay': ([(1, 1)], [1])}
    },
    'constrained': {
        'master': {'valid_delay': ([(0, 0), (1, 5), (6, 10)], [5, 3, 1])},
        'slave':  {'ready_delay': ([(0, 0), (1, 5), (6, 10)], [5, 3, 1])}
    },
    'fast': {
        'master': {'valid_delay': ([(0, 0), (1, 5), (6, 10)], [5, 0, 0])},
        'slave':  {'ready_delay': ([(0, 0), (1, 5), (6, 10)], [5, 0, 0])}
    },
    'backtoback': {
        'master': {'valid_delay': ([(0, 0)], [1])},
        'slave':  {'ready_delay': ([(0, 0)], [1])}
    },
    'burst_pause': {
        'master': {'valid_delay': ([(0, 0), (10, 20)], [8, 1])},
        'slave':  {'ready_delay': ([(0, 0), (12, 25)], [8, 1])}
    },
    'slow_producer': {
        'master': {'valid_delay': ([(8, 20)], [1])},
        'slave':  {'ready_delay': ([(8, 20)], [1])}
    },
    'high_throughput': {
        'master': {'valid_delay': ([(0, 1)], [1])},
        'slave':  {'ready_delay': ([(0, 1)], [1])}
    },
    # GAXI-specific patterns (mirrored from gaxi_buffer.py custom profiles)
    'gaxi_stress': {
        'master': {'valid_delay': ([(0, 0), (1, 2), (5, 10), (20, 30)], [3, 4, 2, 1])},
        'slave':  {'ready_delay': ([(0, 0), (1, 2), (5, 10), (20, 30)], [3, 4, 2, 1])}
    },
    'gaxi_pipeline': {
        'master': {'valid_delay': ([(2, 3), (4, 6)], [3, 1])},
        'slave':  {'ready_delay': ([(2, 3), (4, 6)], [3, 1])}
    },
    'gaxi_backpressure': {
        'master': {'valid_delay': ([(0, 0), (30, 50)], [8, 1])},
        'slave':  {'ready_delay': ([(0, 0), (30, 50)], [8, 1])}
    },
    'gaxi_realistic': {
        'master': {'valid_delay': ([(0, 1), (2, 4), (8, 12), (20, 25)], [4, 3, 2, 1])},
        'slave':  {'ready_delay': ([(0, 1), (2, 4), (8, 12), (20, 25)], [4, 3, 2, 1])}
    },
    'gaxi_burst_heavy': {
        'master': {'valid_delay': ([(0, 0), (50, 80)], [15, 1])},
        'slave':  {'ready_delay': ([(0, 0), (50, 80)], [15, 1])}
    },
    'gaxi_fine_grain': {
        'master': {'valid_delay': ([(0, 1), (2, 3), (4, 5), (6, 8)], [4, 3, 2, 1])},
        'slave':  {'ready_delay': ([(0, 1), (2, 3), (4, 5), (6, 8)], [4, 3, 2, 1])}
    }
}
