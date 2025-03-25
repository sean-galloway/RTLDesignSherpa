"""
AXI4 Master Write User Interface Include File

This module provides common definitions, randomizers, and utility functions
for the user-facing interfaces (s_split, s_error) of the AXI4 Master Write module.
"""

from enum import IntFlag
from collections import namedtuple
from CocoTBFramework.components.flex_randomizer import FlexRandomizer

# Split interface definitions
class SplitInfo(namedtuple('SplitInfo', ['addr', 'id', 'cnt'])):
    """Split information from the s_split interface"""
    pass

# Error interface definitions
class ErrorType(IntFlag):
    """Error types reported on the s_error interface"""
    AW_TIMEOUT = 0b0001
    W_TIMEOUT = 0b0010
    B_TIMEOUT = 0b0100
    B_RESP_ERROR = 0b1000

class ErrorInfo(namedtuple('ErrorInfo', ['type', 'addr', 'id'])):
    """Error information from the s_error interface"""
    @property
    def error_type_str(self):
        """Return a string representation of the error type"""
        if self.type == ErrorType.AW_TIMEOUT:
            return "AW_TIMEOUT"
        elif self.type == ErrorType.W_TIMEOUT:
            return "W_TIMEOUT"
        elif self.type == ErrorType.B_TIMEOUT:
            return "B_TIMEOUT"
        elif self.type == ErrorType.B_RESP_ERROR:
            return "B_RESP_ERROR"
        else:
            return f"UNKNOWN({self.type:04b})"

# Split and Error FIFO randomizers
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
def get_split_fifo_field_config(addr_width, id_width):
    """Get field configuration for the split FIFO"""
    return {
        'addr': {
            'bits': addr_width,
            'default': 0,
            'format': 'hex',
            'display_width': addr_width // 4,
            'active_bits': (addr_width-1, 0),
            'description': 'Split Address'
        },
        'id': {
            'bits': id_width,
            'default': 0,
            'format': 'hex',
            'display_width': 2,
            'active_bits': (id_width-1, 0),
            'description': 'Transaction ID'
        },
        'cnt': {
            'bits': 8,
            'default': 0,
            'format': 'dec',
            'display_width': 2,
            'active_bits': (7, 0),
            'description': 'Number of Splits'
        }
    }

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

def generate_split_test_cases(alignment_mask, addr_width, burst_sizes=(0, 1, 2), burst_lengths=(0, 7, 15, 31, 63, 127, 255)):
    """Generate test cases for split testing"""
    test_cases = []

    # Base address to use (pick something in the middle range)
    base_addr = (1 << (addr_width - 1))

    # Generate addresses at different positions relative to boundaries
    test_addresses = generate_test_addresses(base_addr, alignment_mask)

    # Create test cases combining addresses, sizes, and lengths
    for addr in test_addresses:
        for size in burst_sizes:
            for length in burst_lengths:
                # Calculate if this will cross a boundary
                bytes_per_beat = 1 << size
                total_bytes = bytes_per_beat * (length + 1)
                end_addr = addr + total_bytes - 1

                will_split = ((addr // alignment_mask) != (end_addr // alignment_mask))
                expected_splits = 1 + ((end_addr // alignment_mask) - (addr // alignment_mask))

                test_cases.append({
                    'addr': addr,
                    'size': size,
                    'length': length,
                    'will_split': will_split,
                    'expected_splits': expected_splits
                })

    return test_cases

class PerformanceMetrics:
    """Class to track and verify performance metrics"""
    def __init__(self):
        self.expected_transaction_count = 0
        self.expected_byte_count = 0
        self.expected_latency_sum = 0
        self.transaction_counts = []
        self.byte_counts = []
        self.latency_sums = []

    def record_expected(self, transaction_count, byte_count, latency):
        """Record expected metric values"""
        self.expected_transaction_count += transaction_count
        self.expected_byte_count += byte_count
        self.expected_latency_sum += latency

    def record_actual(self, transaction_count, byte_count, latency_sum):
        """Record actual metric values"""
        self.transaction_counts.append(transaction_count)
        self.byte_counts.append(byte_count)
        self.latency_sums.append(latency_sum)

    def verify(self, log=None):
        """Verify metrics against expected values"""
        if not self.transaction_counts:
            if log:
                log.error("No metrics recorded")
            return False

        actual_transaction_count = self.transaction_counts[-1]
        actual_byte_count = self.byte_counts[-1]
        actual_latency_sum = self.latency_sums[-1]

        # Allow some flexibility in latency sum verification
        latency_match = True
        if self.expected_latency_sum > 0:
            ratio = actual_latency_sum / self.expected_latency_sum
            latency_match = (0.5 <= ratio <= 2.0)

        transaction_match = (actual_transaction_count == self.expected_transaction_count)
        byte_match = (actual_byte_count == self.expected_byte_count)

        if log:
            log.info("Performance metrics verification:")
            log.info(f"  Transaction count: expected={self.expected_transaction_count}, actual={actual_transaction_count}, match={transaction_match}")
            log.info(f"  Byte count: expected={self.expected_byte_count}, actual={actual_byte_count}, match={byte_match}")
            log.info(f"  Latency sum: expected={self.expected_latency_sum}, actual={actual_latency_sum}, match={latency_match}")

        return transaction_match and byte_match and latency_match

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
        (ErrorType.AW_TIMEOUT, ErrorType.W_TIMEOUT),
        (ErrorType.AW_TIMEOUT, ErrorType.B_RESP_ERROR),
        (ErrorType.W_TIMEOUT, ErrorType.B_RESP_ERROR),
        (ErrorType.B_TIMEOUT, ErrorType.B_RESP_ERROR),
        # Three errors at once
        (ErrorType.AW_TIMEOUT, ErrorType.W_TIMEOUT, ErrorType.B_RESP_ERROR),
        (ErrorType.AW_TIMEOUT, ErrorType.B_TIMEOUT, ErrorType.B_RESP_ERROR),
        (ErrorType.W_TIMEOUT, ErrorType.B_TIMEOUT, ErrorType.B_RESP_ERROR),
        # All four at once (this is harder to trigger)
        (ErrorType.AW_TIMEOUT, ErrorType.W_TIMEOUT, ErrorType.B_TIMEOUT, ErrorType.B_RESP_ERROR),
    ]
