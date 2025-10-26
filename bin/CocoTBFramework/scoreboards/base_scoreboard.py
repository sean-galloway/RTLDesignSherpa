# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: BaseScoreboard
# Purpose: Base Scoreboard for verification components
#
# Documentation: bin/CocoTBFramework/README.md
# Subsystem: framework
#
# Author: sean galloway
# Created: 2025-10-18

"""Base Scoreboard for verification components"""
from collections import deque


class BaseScoreboard:
    """Base class for all protocol scoreboards"""

    def __init__(self, name, log=None):
        self.name = name
        self.log = log
        self.expected_queue = deque()
        self.actual_queue = deque()
        self.error_count = 0
        self.transaction_count = 0
        self.mismatched = []
        self.transformer = None

    def add_expected(self, transaction):
        """Add transaction to expected queue"""
        if self.transformer:
            transformed_transactions = self.transformer.transform(transaction)
            for trans in transformed_transactions:
                self.expected_queue.append(trans)
        else:
            self.expected_queue.append(transaction)

    def add_actual(self, transaction):
        """Add transaction to actual queue and trigger comparison"""
        self.actual_queue.append(transaction)
        self.transaction_count += 1
        self._compare_next()

    def _compare_next(self):
        """Compare next transaction in queues if available"""
        if not self.expected_queue or not self.actual_queue:
            return

        expected = self.expected_queue.popleft()
        actual = self.actual_queue.popleft()

        if not self._compare_transactions(expected, actual):
            self.error_count += 1
            self.mismatched.append((expected, actual))  # Store mismatched pair
            self._log_mismatch(expected, actual)

    def _compare_transactions(self, expected, actual):
        """Compare two transactions - override in derived classes"""
        raise NotImplementedError

    def _log_mismatch(self, expected, actual):
        """Log detailed information about mismatched transactions"""
        if self.log:
            self.log.error(f"{self.name} - Transaction mismatch:")
            self.log.error(f"  Expected: {expected}")
            self.log.error(f"  Actual:   {actual}")

    def report(self):
        """Generate report of scoreboard activity"""
        leftover_expected = len(self.expected_queue)
        leftover_actual = len(self.actual_queue)

        if leftover_expected > 0 and self.log:
            self.log.error(f"{self.name} - {leftover_expected} expected transactions not received")

        if leftover_actual > 0 and self.log:
            self.log.error(f"{self.name} - {leftover_actual} actual transactions without matching expected")

        total_errors = self.error_count + leftover_expected + leftover_actual

        if self.log:
            self.log.info(f"{self.name} - Scoreboard summary:")
            self.log.info(f"  Transactions: {self.transaction_count}")
            self.log.info(f"  Errors: {total_errors}")

        return total_errors

    def result(self):
        """
        Calculate the result as a ratio of successful transactions.

        Returns:
            float: Pass rate from 0.0 to 1.0
        """
        total = self.transaction_count
        # Account for expected transactions that haven't been received yet
        total += len(self.expected_queue)

        if total == 0:
            return 1.0  # Perfect score if no transactions expected

        # Calculate failures: mismatches + leftover expected/actual
        failures = self.error_count + len(self.expected_queue) + len(self.actual_queue)

        # Return success ratio
        return (total - failures) / total

    def set_transformer(self, transformer):
        """Set a protocol transformer for the scoreboard"""
        self.transformer = transformer

    def clear(self):
        """Clear all queues and reset counters"""
        self.expected_queue.clear()
        self.actual_queue.clear()
        self.error_count = 0
        self.transaction_count = 0


class ProtocolTransformer:
    """
    Base class for protocol transformers.

    Protocol transformers convert transactions from one protocol to another,
    allowing for cross-protocol comparison in scoreboards.
    """

    def __init__(self, source_type, target_type, log=None):
        """
        Initialize the transformer.

        Args:
            source_type: Source protocol type
            target_type: Target protocol type
            log: Logger instance
        """
        self.source_type = source_type
        self.target_type = target_type
        self.log = log

        # Statistics
        self.num_transformations = 0
        self.num_failures = 0

    def transform(self, transaction):
        """
        Transform a transaction from source to target protocol.

        Args:
            transaction: Source transaction to transform

        Returns:
            List of target transactions (can be empty if transformation fails)
        """
        # Base implementation - subclasses should override
        self.num_failures += 1
        if self.log:
            self.log.error(f"Transform method not implemented for {self.source_type} to {self.target_type}")
        return []

    def try_transform(self, transaction):
        """
        Attempt to transform a transaction with error handling.

        Args:
            transaction: Source transaction to transform

        Returns:
            List of target transactions (empty if transformation fails)
        """
        try:
            result = self.transform(transaction)
            if result:
                self.num_transformations += 1
            else:
                self.num_failures += 1
                if self.log:
                    self.log.warning(f"Transformation from {self.source_type} to {self.target_type} returned empty result")
            return result
        except Exception as e:
            self.num_failures += 1
            if self.log:
                self.log.error(f"Transformation from {self.source_type} to {self.target_type} failed: {str(e)}")
            return []

    def report(self):
        """
        Generate a report of transformer statistics.

        Returns:
            String with report information
        """
        report = [
            f"{self.source_type} to {self.target_type} Transformer Report",
            f"  Successful transformations: {self.num_transformations}",
            f"  Failed transformations: {self.num_failures}"
        ]
        return "\n".join(report)