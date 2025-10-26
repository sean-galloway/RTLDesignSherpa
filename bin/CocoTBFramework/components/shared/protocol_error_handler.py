# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: ErrorHandler
# Purpose: Protocol Error Handler
#
# Documentation: bin/CocoTBFramework/README.md
# Subsystem: framework
#
# Author: sean galloway
# Created: 2025-10-18

"""
Protocol Error Handler

A generic error handler that can be used with various protocol implementations
to inject errors at specific addresses or address ranges.
"""

class ErrorHandler:
    """
    Error response handler for protocol transactions.

    This class manages error responses for specific addresses, ID values,
    or address ranges, allowing fine-grained control over error injection.
    """

    def __init__(self):
        """Initialize the error handler"""
        # Dictionary to track error regions
        self.error_regions = []

        # Dictionary to track individual address/ID pairs that should return errors
        self.error_transactions = {}  # Key: (addr, id), Value: response_code

        # Track statistics
        self.stats = {
            'error_regions_registered': 0,
            'error_transactions_registered': 0,
            'errors_triggered': 0
        }

    def register_error_region(self, start_address, end_address, response_code=2):
        """
        Register a memory region that should return errors.

        Args:
            start_address: Start address of the region
            end_address: End address of the region
            response_code: Error response code (default: 2/SLVERR)
                0: OKAY - Normal successful completion
                1: EXOKAY - Exclusive access success (protocol-specific)
                2: SLVERR - Slave error
                3: DECERR - Decode error
        """
        self.error_regions.append((start_address, end_address, response_code))
        self.stats['error_regions_registered'] += 1

    def register_error_transaction(self, address, id_value=None, response_code=2):
        """
        Register a specific address/ID combination for error response.

        Args:
            address: Target address
            id_value: Transaction ID (None for any ID)
            response_code: Error response code (default: 2/SLVERR)
        """
        key = (address, id_value)  # If id_value is None, applies to any ID
        self.error_transactions[key] = response_code
        self.stats['error_transactions_registered'] += 1

    def clear_error_regions(self):
        """Clear all registered error regions"""
        count = len(self.error_regions)
        self.error_regions = []
        self.stats['error_regions_registered'] -= count

    def clear_error_transactions(self):
        """Clear all registered error transactions"""
        count = len(self.error_transactions)
        self.error_transactions = {}
        self.stats['error_transactions_registered'] -= count

    def clear_all_errors(self):
        """Clear all registered errors (regions and transactions)"""
        self.clear_error_regions()
        self.clear_error_transactions()

    def check_for_error(self, address, id_value=None):
        """
        Check if a transaction should return an error.

        Args:
            address: Target address
            id_value: Transaction ID (optional)

        Returns:
            Tuple of (should_error, response_code)
        """
        # Check for specific transaction errors first
        key = (address, id_value)
        if key in self.error_transactions:
            self.stats['errors_triggered'] += 1
            return True, self.error_transactions[key]

        # Check for errors based on address alone
        key = (address, None)
        if key in self.error_transactions:
            self.stats['errors_triggered'] += 1
            return True, self.error_transactions[key]

        # Check if address is in any error region
        for start_addr, end_addr, resp_code in self.error_regions:
            if start_addr <= address <= end_addr:
                self.stats['errors_triggered'] += 1
                return True, resp_code

        # No error
        return False, 0

    def get_stats(self):
        """
        Get statistics about error regions and transactions.

        Returns:
            Dictionary with statistics
        """
        return self.stats.copy()
