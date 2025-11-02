# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: MonitorStatistics
# Purpose: Robust statistics class for Monitor components
#
# Documentation: bin/CocoTBFramework/README.md
# Subsystem: framework
#
# Author: sean galloway
# Created: 2025-10-18

class MonitorStatistics:
    """Robust statistics class for Monitor components"""

    def __init__(self):
        self.received_transactions = 0
        self.transactions_observed = 0
        self.protocol_violations = 0
        self.x_z_violations = 0
        self.empty_cycles = 0
        self.full_cycles = 0
        self.read_while_empty = 0
        self.write_while_full = 0

    def get_stats(self):
        """
        Return all statistics as a dictionary.

        This makes the class more robust by providing a standard interface
        for accessing statistics without having to manually extract attributes.

        Returns:
            Dictionary containing all statistics
        """
        return {
            'received_transactions': self.received_transactions,
            'transactions_observed': self.transactions_observed,
            'protocol_violations': self.protocol_violations,
            'x_z_violations': self.x_z_violations,
            'empty_cycles': self.empty_cycles,
            'full_cycles': self.full_cycles,
            'read_while_empty': self.read_while_empty,
            'write_while_full': self.write_while_full
        }

    def reset(self):
        """Reset all statistics to zero"""
        self.received_transactions = 0
        self.transactions_observed = 0
        self.protocol_violations = 0
        self.x_z_violations = 0
        self.empty_cycles = 0
        self.full_cycles = 0
        self.read_while_empty = 0
        self.write_while_full = 0

    def __str__(self):
        """Human-readable string representation"""
        return (f"MonitorStats: {self.received_transactions} received, "
                f"{self.protocol_violations} violations, "
                f"{self.x_z_violations} X/Z")

    def __repr__(self):
        """Detailed representation for debugging"""
        return f"MonitorStatistics({self.get_stats()})"