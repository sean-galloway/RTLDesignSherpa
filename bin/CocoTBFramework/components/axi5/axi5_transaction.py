# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: AXI5Transaction
# Purpose: AXI5 Transaction tracking class.
#
# Documentation: bin/CocoTBFramework/README.md
# Subsystem: framework
#
# Author: sean galloway
# Created: 2025-12-15

"""
AXI5 Transaction - Transaction tracking for AXI5 operations.

This module provides the AXI5Transaction class that tracks complete AXI5
transactions including all AXI5-specific features like atomic operations,
memory tagging, and chunking.

Key Design Principles:
1. Complete tracking of AXI5 transaction state
2. Support for atomic operations via ATOP
3. Memory Tagging Extension (MTE) tracking
4. Chunked transfer support
5. MPAM and MECID context tracking
"""

import time
from typing import Optional, List, Any


class AXI5Transaction:
    """Represents a single AXI5 transaction with all related packets."""

    def __init__(self, transaction_id: int, transaction_type: str):
        """
        Initialize an AXI5 transaction.

        Args:
            transaction_id: Unique identifier for this transaction
            transaction_type: 'write', 'read', or 'atomic'
        """
        self.transaction_id = transaction_id
        self.transaction_type = transaction_type  # 'write', 'read', or 'atomic'
        self.start_time = time.time()
        self.end_time = None
        self.is_complete = False

        # Transaction packets
        self.address_packet = None      # AW or AR packet
        self.data_packets = []          # W packets (for writes)
        self.response_packets = []      # B or R packets

        # Transaction state
        self.expected_beats = 1         # Number of data beats expected
        self.received_beats = 0         # Number of data beats received
        self.error_response = None      # First error response received

        # AXI5-specific state
        self.is_atomic = False          # True if this is an atomic operation
        self.atomic_type = None         # ATOP value if atomic
        self.has_poison = False         # True if any data packet has poison
        self.tag_operation = None       # TAGOP value
        self.tag_match_result = None    # Tag match result from response
        self.is_chunked = False         # True if chunking is enabled
        self.chunk_info = []            # List of (chunknum, chunkstrb) tuples
        self.trace_enabled = False      # True if trace is enabled
        self.nsaid = None               # Non-secure access ID
        self.mpam = None                # Memory partitioning info
        self.mecid = None               # Memory encryption context ID

    def add_address_packet(self, packet: Any) -> None:
        """
        Add the address packet (AW or AR).

        Args:
            packet: The address channel packet
        """
        self.address_packet = packet

        # Extract burst length
        if hasattr(packet, 'len'):
            self.expected_beats = packet.len + 1  # AXI len is 0-based

        # Extract AXI5-specific fields
        if hasattr(packet, 'atop') and packet.atop != 0:
            self.is_atomic = True
            self.atomic_type = packet.atop
            self.transaction_type = 'atomic'

        if hasattr(packet, 'tagop'):
            self.tag_operation = packet.tagop

        if hasattr(packet, 'chunken') and packet.chunken:
            self.is_chunked = True

        if hasattr(packet, 'trace') and packet.trace:
            self.trace_enabled = True

        if hasattr(packet, 'nsaid'):
            self.nsaid = packet.nsaid

        if hasattr(packet, 'mpam'):
            self.mpam = packet.mpam

        if hasattr(packet, 'mecid'):
            self.mecid = packet.mecid

    def add_data_packet(self, packet: Any) -> None:
        """
        Add a data packet (W).

        Args:
            packet: The write data channel packet
        """
        self.data_packets.append(packet)

        # Check for poison
        if hasattr(packet, 'poison') and packet.poison:
            self.has_poison = True

    def add_response_packet(self, packet: Any) -> None:
        """
        Add a response packet (B or R).

        Args:
            packet: The response channel packet (B or R)
        """
        self.response_packets.append(packet)
        self.received_beats += 1

        # Check for error responses
        if hasattr(packet, 'resp') and packet.resp != 0:
            if self.error_response is None:
                self.error_response = packet.resp

        # Check for poison (R channel)
        if hasattr(packet, 'poison') and packet.poison:
            self.has_poison = True

        # Check for tag match result
        if hasattr(packet, 'tagmatch'):
            self.tag_match_result = packet.tagmatch

        # Collect chunk info (R channel)
        if hasattr(packet, 'chunkv') and packet.chunkv:
            chunknum = getattr(packet, 'chunknum', 0)
            chunkstrb = getattr(packet, 'chunkstrb', 0)
            self.chunk_info.append((chunknum, chunkstrb))

        # Check if transaction is complete
        if self.transaction_type in ('write', 'atomic'):
            # Write/atomic complete when we get B response
            self.is_complete = True
            self.end_time = time.time()
        elif self.transaction_type == 'read':
            # Read complete when we get R response with RLAST
            if hasattr(packet, 'last') and packet.last:
                self.is_complete = True
                self.end_time = time.time()

    @property
    def duration(self) -> Optional[float]:
        """Get transaction duration in seconds."""
        if self.end_time:
            return self.end_time - self.start_time
        return None

    @property
    def has_error(self) -> bool:
        """Check if transaction had any error responses."""
        return self.error_response is not None

    @property
    def response_code(self) -> str:
        """Get human-readable response code."""
        if self.error_response is None:
            return "OKAY"
        resp_codes = {0: "OKAY", 1: "EXOKAY", 2: "SLVERR", 3: "DECERR"}
        return resp_codes.get(self.error_response, f"UNKNOWN({self.error_response})")

    @property
    def tag_operation_name(self) -> Optional[str]:
        """Get human-readable tag operation name."""
        if self.tag_operation is None:
            return None
        tagop_names = {0: "Invalid", 1: "Transfer", 2: "Update", 3: "Match"}
        return tagop_names.get(self.tag_operation, f"Unknown({self.tag_operation})")

    @property
    def atomic_operation_name(self) -> Optional[str]:
        """Get human-readable atomic operation name."""
        if not self.is_atomic or self.atomic_type is None:
            return None

        # ATOP encoding (partial - common operations)
        atop_names = {
            0x00: "Non-atomic",
            0x10: "AtomicStore",
            0x20: "AtomicLoad",
            0x30: "AtomicSwap",
            0x31: "AtomicCompare",
        }
        return atop_names.get(self.atomic_type, f"Atomic({self.atomic_type:#04x})")

    def get_data_bytes(self) -> bytes:
        """
        Get all data bytes from data packets (for writes) or response packets (for reads).

        Returns:
            Concatenated data bytes
        """
        if self.transaction_type == 'write':
            packets = self.data_packets
        else:
            packets = self.response_packets

        data_bytes = bytearray()
        for packet in packets:
            if hasattr(packet, 'data'):
                # Convert data to bytes (assuming it's an integer)
                data = packet.data
                data_width = data.bit_length() if data else 8
                byte_width = max(1, (data_width + 7) // 8)
                data_bytes.extend(data.to_bytes(byte_width, byteorder='little'))

        return bytes(data_bytes)

    def __repr__(self) -> str:
        """String representation for debugging."""
        status = "complete" if self.is_complete else "pending"
        error_str = f", error={self.response_code}" if self.has_error else ""
        atomic_str = f", atomic={self.atomic_operation_name}" if self.is_atomic else ""
        tag_str = f", tagop={self.tag_operation_name}" if self.tag_operation else ""
        poison_str = ", POISONED" if self.has_poison else ""

        return (
            f"AXI5Transaction(id={self.transaction_id}, type={self.transaction_type}, "
            f"status={status}, beats={self.received_beats}/{self.expected_beats}"
            f"{error_str}{atomic_str}{tag_str}{poison_str})"
        )


class AXI5TransactionTracker:
    """Tracks multiple AXI5 transactions by ID."""

    def __init__(self):
        """Initialize the transaction tracker."""
        self.pending_transactions: dict[int, AXI5Transaction] = {}
        self.completed_transactions: List[AXI5Transaction] = []
        self._next_id = 0

    def create_transaction(self, transaction_type: str, transaction_id: Optional[int] = None) -> AXI5Transaction:
        """
        Create a new transaction.

        Args:
            transaction_type: 'write', 'read', or 'atomic'
            transaction_id: Optional specific ID, otherwise auto-generated

        Returns:
            New AXI5Transaction instance
        """
        if transaction_id is None:
            transaction_id = self._next_id
            self._next_id += 1

        txn = AXI5Transaction(transaction_id, transaction_type)
        self.pending_transactions[transaction_id] = txn
        return txn

    def get_transaction(self, transaction_id: int) -> Optional[AXI5Transaction]:
        """
        Get a transaction by ID.

        Args:
            transaction_id: The transaction ID

        Returns:
            The transaction or None if not found
        """
        return self.pending_transactions.get(transaction_id)

    def complete_transaction(self, transaction_id: int) -> Optional[AXI5Transaction]:
        """
        Mark a transaction as complete and move to completed list.

        Args:
            transaction_id: The transaction ID

        Returns:
            The completed transaction or None if not found
        """
        txn = self.pending_transactions.pop(transaction_id, None)
        if txn:
            self.completed_transactions.append(txn)
        return txn

    def get_statistics(self) -> dict:
        """
        Get transaction statistics.

        Returns:
            Dictionary with statistics
        """
        all_txns = list(self.pending_transactions.values()) + self.completed_transactions

        stats = {
            'total': len(all_txns),
            'pending': len(self.pending_transactions),
            'completed': len(self.completed_transactions),
            'writes': sum(1 for t in all_txns if t.transaction_type == 'write'),
            'reads': sum(1 for t in all_txns if t.transaction_type == 'read'),
            'atomics': sum(1 for t in all_txns if t.transaction_type == 'atomic'),
            'errors': sum(1 for t in all_txns if t.has_error),
            'poisoned': sum(1 for t in all_txns if t.has_poison),
            'tag_operations': sum(1 for t in all_txns if t.tag_operation is not None),
        }

        # Calculate average duration for completed transactions
        durations = [t.duration for t in self.completed_transactions if t.duration is not None]
        if durations:
            stats['avg_duration'] = sum(durations) / len(durations)
            stats['min_duration'] = min(durations)
            stats['max_duration'] = max(durations)

        return stats

    def clear(self) -> None:
        """Clear all transactions."""
        self.pending_transactions.clear()
        self.completed_transactions.clear()
        self._next_id = 0
