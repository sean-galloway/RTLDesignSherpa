# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: MasterStatistics
# Purpose: Master/Slave Statistics Classes for BFM Components
#
# Documentation: bin/CocoTBFramework/README.md
# Subsystem: framework
#
# Author: sean galloway
# Created: 2025-10-18

"""
Master/Slave Statistics Classes for BFM Components

Provides consistent statistics collection across all master and slave components,
complementing the existing MonitorStatistics class.
"""
import time
from typing import Dict, Any, Optional
from collections import deque


class MasterStatistics:
    """Statistics tracking for Master components (writers/drivers)"""

    def __init__(self, window_size: int = 100):
        """
        Initialize master statistics.

        Args:
            window_size: Number of recent transactions to track for moving averages
        """
        # Transaction counts
        self.transactions_sent = 0
        self.transactions_completed = 0
        self.transactions_failed = 0
        self.bytes_transferred = 0

        # Protocol and flow control
        self.protocol_violations = 0
        self.timeout_events = 0
        self.retry_attempts = 0
        self.flow_control_stalls = 0
        self.backpressure_cycles = 0

        # Performance metrics
        self.total_latency = 0.0
        self.peak_throughput = 0.0
        self.start_time = time.time()

        # Moving window for recent performance tracking
        self.window_size = window_size
        self.recent_latencies = deque(maxlen=window_size)
        self.recent_throughputs = deque(maxlen=window_size)
        self.last_throughput_time = time.time()
        self.last_transaction_count = 0

        # Error tracking
        self.error_types = {}
        self.last_error_time = None
        self.last_error_message = None

    def record_transaction_start(self) -> float:
        """
        Record the start of a transaction.

        Returns:
            Transaction start timestamp for latency calculation
        """
        self.transactions_sent += 1
        return time.time()

    def record_transaction_complete(self, start_time: float, bytes_count: int = 0):
        """
        Record completion of a transaction.

        Args:
            start_time: Transaction start timestamp from record_transaction_start()
            bytes_count: Number of bytes transferred in this transaction
        """
        self.transactions_completed += 1
        self.bytes_transferred += bytes_count

        # Calculate and record latency
        latency = time.time() - start_time
        self.total_latency += latency
        self.recent_latencies.append(latency)

    def record_transaction_failed(self, error_type: str, error_message: str = ""):
        """
        Record a failed transaction.

        Args:
            error_type: Type/category of error
            error_message: Detailed error message
        """
        self.transactions_failed += 1

        # Track error types
        if error_type not in self.error_types:
            self.error_types[error_type] = 0
        self.error_types[error_type] += 1

        # Record last error for debugging
        self.last_error_time = time.time()
        self.last_error_message = f"{error_type}: {error_message}"

    def record_protocol_violation(self, violation_type: str):
        """Record a protocol violation."""
        self.protocol_violations += 1
        self.record_transaction_failed("protocol_violation", violation_type)

    def record_timeout(self):
        """Record a timeout event."""
        self.timeout_events += 1
        self.record_transaction_failed("timeout", "Transaction timeout")

    def record_retry(self):
        """Record a retry attempt."""
        self.retry_attempts += 1

    def record_flow_control_stall(self, cycles: int = 1):
        """
        Record flow control stalls (backpressure).

        Args:
            cycles: Number of clock cycles stalled
        """
        self.flow_control_stalls += 1
        self.backpressure_cycles += cycles

    def update_throughput(self):
        """Update throughput calculations (call periodically)."""
        current_time = time.time()
        time_delta = current_time - self.last_throughput_time

        if time_delta >= 1.0:  # Update every second
            transaction_delta = self.transactions_completed - self.last_transaction_count
            current_throughput = transaction_delta / time_delta

            self.recent_throughputs.append(current_throughput)
            if current_throughput > self.peak_throughput:
                self.peak_throughput = current_throughput

            self.last_throughput_time = current_time
            self.last_transaction_count = self.transactions_completed

    def get_average_latency(self) -> float:
        """Get average latency across all transactions."""
        if self.transactions_completed > 0:
            return self.total_latency / self.transactions_completed
        return 0.0

    def get_recent_average_latency(self) -> float:
        """Get average latency for recent transactions."""
        if self.recent_latencies:
            return sum(self.recent_latencies) / len(self.recent_latencies)
        return 0.0

    def get_current_throughput(self) -> float:
        """Get current throughput (transactions per second)."""
        if self.recent_throughputs:
            return self.recent_throughputs[-1]
        return 0.0

    def get_average_throughput(self) -> float:
        """Get average throughput across all time."""
        elapsed_time = time.time() - self.start_time
        if elapsed_time > 0:
            return self.transactions_completed / elapsed_time
        return 0.0

    def get_success_rate(self) -> float:
        """Get transaction success rate as percentage."""
        total_attempts = self.transactions_sent
        if total_attempts > 0:
            return (self.transactions_completed / total_attempts) * 100.0
        return 100.0

    def get_stats(self) -> Dict[str, Any]:
        """
        Get comprehensive statistics dictionary.

        Returns:
            Dictionary containing all statistics
        """
        self.update_throughput()  # Ensure throughput is current

        return {
            # Transaction counts
            'transactions_sent': self.transactions_sent,
            'transactions_completed': self.transactions_completed,
            'transactions_failed': self.transactions_failed,
            'bytes_transferred': self.bytes_transferred,
            'success_rate_percent': self.get_success_rate(),

            # Performance metrics
            'average_latency_ms': self.get_average_latency() * 1000,
            'recent_average_latency_ms': self.get_recent_average_latency() * 1000,
            'current_throughput_tps': self.get_current_throughput(),
            'average_throughput_tps': self.get_average_throughput(),
            'peak_throughput_tps': self.peak_throughput,

            # Protocol and flow control
            'protocol_violations': self.protocol_violations,
            'timeout_events': self.timeout_events,
            'retry_attempts': self.retry_attempts,
            'flow_control_stalls': self.flow_control_stalls,
            'backpressure_cycles': self.backpressure_cycles,

            # Error information
            'error_types': self.error_types.copy(),
            'last_error_time': self.last_error_time,
            'last_error_message': self.last_error_message,

            # Operational info
            'uptime_seconds': time.time() - self.start_time,
            'window_size': self.window_size
        }

    def reset(self):
        """Reset all statistics to initial state."""
        self.__init__(self.window_size)

    def __str__(self) -> str:
        """Human-readable string representation."""
        stats = self.get_stats()
        return (
            f"MasterStats: {stats['transactions_completed']}/{stats['transactions_sent']} "
            f"({stats['success_rate_percent']:.1f}% success), "
            f"Avg Latency: {stats['average_latency_ms']:.2f}ms, "
            f"Throughput: {stats['current_throughput_tps']:.1f} tps"
        )


class SlaveStatistics:
    """Statistics tracking for Slave components (readers/responders)"""

    def __init__(self, window_size: int = 100):
        """
        Initialize slave statistics.

        Args:
            window_size: Number of recent transactions to track for moving averages
        """
        # Transaction counts
        self.transactions_received = 0
        self.transactions_processed = 0
        self.transactions_rejected = 0
        self.bytes_received = 0

        # Response statistics
        self.responses_sent = 0
        self.response_errors = 0
        self.average_processing_time = 0.0

        # Protocol violations and errors
        self.protocol_violations = 0
        self.malformed_requests = 0
        self.buffer_overruns = 0
        self.buffer_underruns = 0

        # Performance tracking
        self.start_time = time.time()
        self.window_size = window_size
        self.recent_processing_times = deque(maxlen=window_size)
        self.peak_processing_rate = 0.0

        # Error tracking
        self.error_types = {}
        self.last_error_time = None
        self.last_error_message = None

    def record_transaction_received(self, bytes_count: int = 0) -> float:
        """
        Record receipt of a new transaction.

        Args:
            bytes_count: Number of bytes in the transaction

        Returns:
            Timestamp for processing time calculation
        """
        self.transactions_received += 1
        self.bytes_received += bytes_count
        return time.time()

    def record_transaction_processed(self, start_time: float):
        """
        Record successful processing of a transaction.

        Args:
            start_time: Processing start timestamp
        """
        self.transactions_processed += 1
        processing_time = time.time() - start_time
        self.recent_processing_times.append(processing_time)

    def record_transaction_rejected(self, reason: str):
        """
        Record rejection of a transaction.

        Args:
            reason: Reason for rejection
        """
        self.transactions_rejected += 1
        if reason not in self.error_types:
            self.error_types[reason] = 0
        self.error_types[reason] += 1

        self.last_error_time = time.time()
        self.last_error_message = f"Transaction rejected: {reason}"

    def record_response_sent(self, success: bool = True):
        """
        Record a response sent back to master.

        Args:
            success: Whether the response was successful
        """
        self.responses_sent += 1
        if not success:
            self.response_errors += 1

    def record_protocol_violation(self, violation_type: str):
        """Record a protocol violation."""
        self.protocol_violations += 1
        self.record_transaction_rejected(f"Protocol violation: {violation_type}")

    def record_malformed_request(self):
        """Record a malformed request."""
        self.malformed_requests += 1
        self.record_transaction_rejected("Malformed request")

    def record_buffer_overrun(self):
        """Record a buffer overrun condition."""
        self.buffer_overruns += 1
        self.record_transaction_rejected("Buffer overrun")

    def record_buffer_underrun(self):
        """Record a buffer underrun condition."""
        self.buffer_underruns += 1

    def get_processing_rate(self) -> float:
        """Get current processing rate (transactions per second)."""
        elapsed_time = time.time() - self.start_time
        if elapsed_time > 0:
            return self.transactions_processed / elapsed_time
        return 0.0

    def get_average_processing_time(self) -> float:
        """Get average processing time for recent transactions."""
        if self.recent_processing_times:
            return sum(self.recent_processing_times) / len(self.recent_processing_times)
        return 0.0

    def get_acceptance_rate(self) -> float:
        """Get transaction acceptance rate as percentage."""
        total_received = self.transactions_received
        if total_received > 0:
            return (self.transactions_processed / total_received) * 100.0
        return 100.0

    def get_stats(self) -> Dict[str, Any]:
        """
        Get comprehensive statistics dictionary.

        Returns:
            Dictionary containing all statistics
        """
        return {
            # Transaction counts
            'transactions_received': self.transactions_received,
            'transactions_processed': self.transactions_processed,
            'transactions_rejected': self.transactions_rejected,
            'bytes_received': self.bytes_received,
            'acceptance_rate_percent': self.get_acceptance_rate(),

            # Response statistics
            'responses_sent': self.responses_sent,
            'response_errors': self.response_errors,
            'response_success_rate_percent': (
                ((self.responses_sent - self.response_errors) / max(1, self.responses_sent)) * 100.0
            ),

            # Performance metrics
            'processing_rate_tps': self.get_processing_rate(),
            'average_processing_time_ms': self.get_average_processing_time() * 1000,
            'peak_processing_rate_tps': self.peak_processing_rate,

            # Error statistics
            'protocol_violations': self.protocol_violations,
            'malformed_requests': self.malformed_requests,
            'buffer_overruns': self.buffer_overruns,
            'buffer_underruns': self.buffer_underruns,
            'error_types': self.error_types.copy(),
            'last_error_time': self.last_error_time,
            'last_error_message': self.last_error_message,

            # Operational info
            'uptime_seconds': time.time() - self.start_time,
            'window_size': self.window_size
        }

    def reset(self):
        """Reset all statistics to initial state."""
        self.__init__(self.window_size)

    def __str__(self) -> str:
        """Human-readable string representation."""
        stats = self.get_stats()
        return (
            f"SlaveStats: {stats['transactions_processed']}/{stats['transactions_received']} "
            f"({stats['acceptance_rate_percent']:.1f}% accepted), "
            f"Processing: {stats['average_processing_time_ms']:.2f}ms, "
            f"Rate: {stats['processing_rate_tps']:.1f} tps"
        )


# Compatibility alias for backward compatibility
class ComponentStatistics(MasterStatistics):
    """Alias for MasterStatistics for backward compatibility."""
    pass
