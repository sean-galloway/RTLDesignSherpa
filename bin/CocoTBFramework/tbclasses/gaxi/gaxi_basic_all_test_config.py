"""Configuration classes and constants for GAXI testbenches"""
import os
from dataclasses import dataclass, field


@dataclass
class TestConfig:
    """Configuration parameters for GAXI testbenches"""
    # Core test parameters
    depth: int = 0
    addr_width: int = 0
    ctrl_width: int = 0
    data_width: int = 0
    mode: str = 'skid'
    buffer_type: str = 'standard'  # 'standard', 'multi', 'field', 'async'
    clk_wr_period: int = 10
    clk_rd_period: int = 10
    n_flop_cross: int = 2  # For async buffers

    # Derived limits
    max_addr: int = field(init=False, default=0)
    max_ctrl: int = field(init=False, default=0)
    max_data: int = field(init=False, default=0)

    # Test control
    timeout_cycles: int = 1000
    seed: int = 0

    def __post_init__(self):
        """Calculate derived values after initialization"""
        self.max_addr = (2**self.addr_width)-1 if self.addr_width > 0 else 0
        self.max_ctrl = (2**self.ctrl_width)-1 if self.ctrl_width > 0 else 0
        self.max_data = (2**self.data_width)-1 if self.data_width > 0 else 0

    @classmethod
    def from_env(cls):
        """Create configuration from environment variables"""
        buffer_type = os.environ.get('BUFFER_TYPE', 'standard')
        mode = os.environ.get('TEST_MODE', 'skid')

        # Adjust mode for skid buffer types which only support 'skid' mode
        if buffer_type == 'standard' and 'skid' in os.environ.get('DUT', ''):
            mode = 'skid'

        return cls(
            depth=int(os.environ.get('TEST_DEPTH', '0')),
            addr_width=int(os.environ.get('TEST_ADDR_WIDTH', '0')),
            ctrl_width=int(os.environ.get('TEST_CTRL_WIDTH', '0')),
            data_width=int(os.environ.get('TEST_WIDTH', '0')),
            mode=mode,
            buffer_type=buffer_type,
            clk_wr_period=int(os.environ.get('TEST_CLK_WR', '10')),
            clk_rd_period=int(os.environ.get('TEST_CLK_RD', '10')),
            n_flop_cross=int(os.environ.get('TEST_N_FLOP_CROSS', '2')),
            timeout_cycles=1000,
            seed=int(os.environ.get('SEED', '0'))
        )


# Helper functions for determining buffer configuration
def get_is_async(buffer_type, dut_name):
    """
    Determine if this is an async buffer design.

    Args:
        buffer_type: Buffer type string
        dut_name: Device under test name

    Returns:
        True if async design, False otherwise
    """
    return (buffer_type == 'async') or ('async' in dut_name.lower())


def get_field_mode(buffer_type, dut_name):
    """
    Determine the field mode based on buffer type and DUT name.

    Args:
        buffer_type: Buffer type string
        dut_name: Device under test name

    Returns:
        Field mode: 'standard', 'multi', or 'multi_data'
    """
    # Check for multi-data mode first (highest priority)
    if 'multi_data' in dut_name.lower() or ('data0' in dut_name.lower() and 'data1' in dut_name.lower()):
        return 'multi_data'

    # Check for multi-signal mode
    if buffer_type in ['multi', 'field'] or 'multi' in dut_name.lower():
        return 'multi'

    # Default to standard mode
    return 'standard'


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

    # Multi-signal mode - addr, ctrl, data fields
    'multi': {
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
        'data': {
            'bits': 32,  # Will be updated based on config
            'default': 0,
            'format': 'hex',
            'display_width': 4,
            'active_bits': (31, 0),  # Will be updated based on config
            'description': 'Data value'
        }
    },

    # Multi-data mode - addr, ctrl, data0, data1 fields
    'multi_data': {
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

# Randomizer configurations
RANDOMIZER_CONFIGS = {
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
