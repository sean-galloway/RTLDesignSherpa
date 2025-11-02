# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: AXI4Transaction
# Purpose: AXI4 Master - Clean implementation using multiple AXI4Channels.
#
# Documentation: bin/CocoTBFramework/README.md
# Subsystem: framework
#
# Author: sean galloway
# Created: 2025-10-18

"""
AXI4 Master - Clean implementation using multiple AXI4Channels.

This module provides the AXI4Master class that coordinates multiple AXI4Channel objects
to implement complete AXI4 master functionality with transaction tracking and
simple high-level APIs.

Key Design Principles:
1. Composition of AXI4Channel objects
2. Transaction coordination between related channels
3. Simple, intuitive APIs (write_single, read_single)
4. Proper ID management and response tracking
5. Clean integration with existing infrastructure
"""

import time
import asyncio
from typing import Dict, List, Optional, Any, Callable
from ..shared.packet import Packet
from .axi4_channel import AXI4Channel


class AXI4Transaction:
    """Represents a single AXI4 transaction with all related packets."""

    def __init__(self, transaction_id: int, transaction_type: str):
        self.transaction_id = transaction_id
        self.transaction_type = transaction_type  # 'write' or 'read'
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

    def add_address_packet(self, packet):
        """Add the address packet (AW or AR)."""
        self.address_packet = packet
        if hasattr(packet, 'awlen') or hasattr(packet, 'arlen'):
            burst_len = getattr(packet, 'awlen', 0) or getattr(packet, 'arlen', 0)
            self.expected_beats = burst_len + 1  # AXI4 len is 0-based

    def add_data_packet(self, packet):
        """Add a data packet (W)."""
        self.data_packets.append(packet)

    def add_response_packet(self, packet):
        """Add a response packet (B or R)."""
        self.response_packets.append(packet)
        self.received_beats += 1

        # Check for error responses
        if hasattr(packet, 'bresp') and packet.bresp != 0:
            self.error_response = packet.bresp
        elif hasattr(packet, 'rresp') and packet.rresp != 0:
            self.error_response = packet.rresp

        # Check if transaction is complete
        if self.transaction_type == 'write':
            # Write complete when we get B response
            self.is_complete = True
            self.end_time = time.time()
        elif self.transaction_type == 'read':
            # Read complete when we get R response with RLAST
            if hasattr(packet, 'rlast') and packet.rlast:
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

