# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: APBSequence
# Purpose: Enhanced APB Sequence class with direct packet generation
#
# Documentation: bin/CocoTBFramework/README.md
# Subsystem: framework
#
# Author: sean galloway
# Created: 2025-10-18

"""Enhanced APB Sequence class with direct packet generation"""
from dataclasses import dataclass, field
from collections import deque
import random
from typing import List, Tuple, Dict, Optional
import copy

from .apb_packet import APBPacket

@dataclass
class APBSequence:
    """Configuration for test patterns with direct packet generation"""
    # Test name
    name: str = "basic"

    # Transaction sequence - list of writes (True) and reads (False)
    # Examples: [True, False] for alternating write-read
    #           [True, True, ..., False, False] for all writes then all reads
    pwrite_seq: List[bool] = field(default_factory=list)

    # Address sequence - list of addresses to use
    # If shorter than pwrite_seq, will cycle through the addresses
    addr_seq: List[int] = field(default_factory=list)

    # Data sequence - list of data values to use for writes
    # If shorter than number of writes, will cycle through the data values
    data_seq: List[int] = field(default_factory=list)

    # Strobe sequence - list of strobe masks to use for writes
    # If shorter than number of writes, will cycle through the strobe masks
    strb_seq: List[int] = field(default_factory=list)

    # Protection attributes sequence
    pprot_seq: List[int] = field(default_factory=list)

    # Timing
    inter_cycle_delays: List[int] = field(default_factory=list)  # Delays between cycles

    # Master timing randomizer
    master_randomizer: Optional[Dict] = None
    slave_randomizer: Optional[Tuple] = None
    other_randomizer: Optional[Tuple] = None

    # Selection mode
    use_random_selection: bool = False  # If True, randomly select from sequences

    # Verification
    verify_data: bool = True

    # Data width for sizing operations
    data_width: int = 32

    # Current transaction count
    transaction_count: int = 0

    def __post_init__(self):
        """Initialize iterators for sequences and defaults"""
        self.pwrite_iter = iter(self.pwrite_seq)
        self.addr_iter = iter(self.addr_seq)
        self.data_iter = iter(self.data_seq)
        self.strb_iter = iter(self.strb_seq)
        self.delay_iter = iter(self.inter_cycle_delays)

        # Default protection values if none provided
        if not self.pprot_seq:
            self.pprot_seq = [0]  # Default protection value
        self.pprot_iter = iter(self.pprot_seq)

    def reset_iterators(self):
        """Reset all iterators to the beginning"""
        self.pwrite_iter = iter(self.pwrite_seq)
        self.addr_iter = iter(self.addr_seq)
        self.data_iter = iter(self.data_seq)
        self.strb_iter = iter(self.strb_seq)
        self.delay_iter = iter(self.inter_cycle_delays)
        self.pprot_iter = iter(self.pprot_seq)
        self.transaction_count = 0

    def next_pwrite(self) -> bool:
        """Get next write/read operation"""
        if self.use_random_selection:
            return random.choice(self.pwrite_seq)
        try:
            return next(self.pwrite_iter)
        except StopIteration:
            self.pwrite_iter = iter(self.pwrite_seq)
            return next(self.pwrite_iter)

    def next_addr(self) -> int:
        """Get next address"""
        if self.use_random_selection:
            return random.choice(self.addr_seq)
        try:
            return next(self.addr_iter)
        except StopIteration:
            self.addr_iter = iter(self.addr_seq)
            return next(self.addr_iter)

    def next_data(self) -> int:
        """Get next data value"""
        if self.use_random_selection:
            return random.choice(self.data_seq)
        try:
            return next(self.data_iter)
        except StopIteration:
            self.data_iter = iter(self.data_seq)
            return next(self.data_iter)

    def next_strb(self) -> int:
        """Get next strobe mask"""
        if self.use_random_selection:
            return random.choice(self.strb_seq)
        try:
            return next(self.strb_iter)
        except StopIteration:
            self.strb_iter = iter(self.strb_seq)
            return next(self.strb_iter)

    def next_pprot(self) -> int:
        """Get next protection attribute"""
        if self.use_random_selection:
            return random.choice(self.pprot_seq)
        try:
            return next(self.pprot_iter)
        except StopIteration:
            self.pprot_iter = iter(self.pprot_seq)
            return next(self.pprot_iter)

    def next_delay(self) -> int:
        """Get next inter-cycle delay"""
        if not self.inter_cycle_delays:
            return 0

        if self.use_random_selection:
            return random.choice(self.inter_cycle_delays)
        try:
            return next(self.delay_iter)
        except StopIteration:
            self.delay_iter = iter(self.inter_cycle_delays)
            return next(self.delay_iter)

    def next(self) -> APBPacket:
        """
        Generate the next complete APB packet

        Returns:
            APBPacket: Complete APB packet object ready for transmission
        """
        # Get next values from sequence
        pwrite = self.next_pwrite()
        paddr = self.next_addr()
        pprot = self.next_pprot()

        # Get strobes and data for writes
        if pwrite:
            pwdata = self.next_data()
            pstrb = self.next_strb()
        else:
            pwdata = 0  # Not used for reads
            pstrb = 0   # Not used for reads

        # Create APB packet
        packet = APBPacket(
            count=self.transaction_count,
            pwrite=1 if pwrite else 0,
            paddr=paddr,
            pwdata=pwdata,
            prdata=0,  # Will be filled by slave for reads
            pstrb=pstrb,
            pprot=pprot,
            pslverr=0   # Will be set by slave if error
        )

        # Increment transaction count
        self.transaction_count += 1

        return copy.copy(packet)

    def has_more_transactions(self) -> bool:
        """
        Check if there are more transactions in the sequence

        Returns:
            bool: True if more transactions are available
        """
        # For unlimited sequences or random selections, always return True
        if self.use_random_selection:
            return True

        # For finite sequences, check if we've reached the end
        return self.transaction_count < len(self.pwrite_seq)
