"""
AXI4 Slave Read User Interface Include File

This module provides common definitions, randomizers, and utility functions
for the user-facing interfaces (m_error) of the AXI4 Slave Read module.
"""

from enum import IntFlag
from collections import namedtuple
from CocoTBFramework.components.flex_randomizer import FlexRandomizer


# Error interface definitions
class ErrorType(IntFlag):
    """Error types reported on the m_error interface"""
    AR_TIMEOUT = 0b0001
    R_TIMEOUT = 0b0010
    R_RESP_ERROR = 0b0100


class ErrorInfo(namedtuple('ErrorInfo', ['type', 'addr', 'id'])):
    """Error information from the m_error interface"""
    @property
    def error_type_str(self):
        """Return a string representation of the error type"""
        if self.type == ErrorType.AR_TIMEOUT:
            return "AR_TIMEOUT"
        elif self.type == ErrorType.R_TIMEOUT:
            return "R_TIMEOUT"
        elif self.type == ErrorType.R_RESP_ERROR:
            return "R_RESP_ERROR"
        else:
            return f"UNKNOWN({self.type:04b})"


# Error FIFO randomizers
FIFO_READY_CONSTRAINTS_ALWAYS = {
    'ready_delay': ([[0, 0]], [1.0])
}

FIFO_READY_CONSTRAINTS_FIXED = {
    'ready_delay': ([[2, 2]], [1.0])
}

FIFO_READY_CONSTRAINTS_FAST = {
    'ready_delay': ([[0, 0], [1, 2]], [0.8, 0.2])
}

FIFO_READY_CONSTRAINTS_SLOW = {
    'ready_delay': ([[0, 0], [1, 5], [6, 10]], [0.2, 0.6, 0.2])
}

FIFO_READY_CONSTRAINTS_VERY_SLOW = {
    'ready_delay': ([[0, 0], [1, 10], [11, 20]], [0.1, 0.4, 0.5])
}


# Utility functions for error injection
def create_error_randomizers():
    """Create a set of randomizers for error injection tests"""
    return {
        'fixed': FlexRandomizer(FIFO_READY_CONSTRAINTS_FIXED),
        'always_ready': FlexRandomizer(FIFO_READY_CONSTRAINTS_ALWAYS),
        'fast_ready': FlexRandomizer(FIFO_READY_CONSTRAINTS_FAST),
        'slow_ready': FlexRandomizer(FIFO_READY_CONSTRAINTS_SLOW),
        'very_slow_ready': FlexRandomizer(FIFO_READY_CONSTRAINTS_VERY_SLOW),
    }


# Field configurations for user interface FIFOs
def get_error_fifo_field_config(addr_width, id_width):
    """Get field configuration for the error FIFO"""
    return {
        'type': {
            'bits': 4,  # 4 bits to match errmon.sv
            'default': 0,
            'format': 'bin',
            'display_width': 4,
            'active_bits': (3, 0),
            'description': 'Error Type'
        },
        'addr': {
            'bits': addr_width,
            'default': 0,
            'format': 'hex',
            'display_width': addr_width // 4,
            'active_bits': (addr_width-1, 0),
            'description': 'Error Address'
        },
        'id': {
            'bits': id_width,
            'default': 0,
            'format': 'hex',
            'display_width': 2,
            'active_bits': (id_width-1, 0),
            'description': 'Transaction ID'
        }
    }


def generate_test_addresses(base_addr, alignment_mask):
    """Generate test addresses relative to an alignment mask"""
    addresses = []
    # Bottom of boundary
    addresses.append(base_addr - (base_addr % alignment_mask))
    # Middle of boundary
    addresses.append(base_addr - (base_addr % alignment_mask) + (alignment_mask // 2))
    # Just before top of boundary
    addresses.append(base_addr - (base_addr % alignment_mask) + alignment_mask - 4)
    # Top of boundary (next boundary bottom)
    addresses.append(base_addr - (base_addr % alignment_mask) + alignment_mask)
    return addresses


# Helper functions for timing tests
def generate_timeout_test_values(base_timeout, count=8):
    """Generate timeout values around the base timeout for testing"""
    test_values = []

    # Generate values below the timeout
    for i in range(1, count//2 + 1):
        factor = 1 - (i / (count//2 + 1))  # Values between 0.5 and 1.0 times the timeout
        test_values.append(int(base_timeout * factor))

    # Generate values above the timeout
    for i in range(1, count//2 + 1):
        factor = 1 + (i / (count//2 + 1))  # Values between 1.0 and 1.5 times the timeout
        test_values.append(int(base_timeout * factor))

    # Sort the values
    test_values.sort()
    return test_values


def create_collision_test_matrix():
    """Create a test matrix for error collision testing"""
    return [
        # Two errors at once
        (ErrorType.AR_TIMEOUT, ErrorType.R_TIMEOUT),
        (ErrorType.AR_TIMEOUT, ErrorType.R_RESP_ERROR),
        (ErrorType.R_TIMEOUT, ErrorType.R_RESP_ERROR),
        # All three at once (this is harder to trigger)
        (ErrorType.AR_TIMEOUT, ErrorType.R_TIMEOUT, ErrorType.R_RESP_ERROR),
    ]
