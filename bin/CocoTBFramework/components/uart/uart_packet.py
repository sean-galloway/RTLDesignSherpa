# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: UARTPacket
# Purpose: UART transaction packet data structure
#
# Documentation: bin/CocoTBFramework/README.md
# Subsystem: framework
#
# Author: sean galloway
# Created: 2025-11-09

"""UART Transaction Packet Class"""

from dataclasses import dataclass, field
from typing import Optional


@dataclass
class UARTPacket:
    """
    UART Transaction Packet

    Represents a single UART byte transmission (start bit + 8 data bits + stop bit).

    Attributes:
        start_time: Simulation time when transmission started (ns)
        count: Transaction counter
        data: 8-bit data value transmitted/received
        parity: Optional parity bit (if parity enabled)
        parity_error: True if parity error detected
        framing_error: True if framing error detected (stop bit not high)
        direction: 'TX' or 'RX' for transmit/receive
    """

    start_time: float = 0.0
    count: int = 0
    data: int = 0
    parity: Optional[int] = None
    parity_error: bool = False
    framing_error: bool = False
    direction: str = 'TX'  # 'TX' or 'RX'

    def __post_init__(self):
        """Validate packet data"""
        assert 0 <= self.data <= 0xFF, f"Data out of range: 0x{self.data:X}"
        assert self.direction in ['TX', 'RX'], f"Invalid direction: {self.direction}"
        if self.parity is not None:
            assert self.parity in [0, 1], f"Invalid parity: {self.parity}"

    def formatted(self, compact=True):
        """
        Format packet for display

        Args:
            compact: If True, single line. If False, multi-line detailed format.

        Returns:
            Formatted string representation
        """
        if compact:
            # Single-line compact format
            error_str = ""
            if self.parity_error:
                error_str += " [PERR]"
            if self.framing_error:
                error_str += " [FERR]"

            parity_str = ""
            if self.parity is not None:
                parity_str = f" P={self.parity}"

            return (f"#{self.count} {self.direction} @ {self.start_time:.1f}ns: "
                    f"0x{self.data:02X} ({chr(self.data) if 32 <= self.data <= 126 else '?'})"
                    f"{parity_str}{error_str}")
        else:
            # Multi-line detailed format
            lines = [
                f"UART Packet #{self.count}:",
                f"  Time:      {self.start_time:.1f} ns",
                f"  Direction: {self.direction}",
                f"  Data:      0x{self.data:02X} ({self.data})",
                f"  ASCII:     '{chr(self.data)}'" if 32 <= self.data <= 126 else "  ASCII:     (non-printable)",
            ]

            if self.parity is not None:
                lines.append(f"  Parity:    {self.parity}")

            if self.parity_error or self.framing_error:
                error_list = []
                if self.parity_error:
                    error_list.append("Parity Error")
                if self.framing_error:
                    error_list.append("Framing Error")
                lines.append(f"  Errors:    {', '.join(error_list)}")

            return '\n'.join(lines)

    def __str__(self):
        """String representation (compact format)"""
        return self.formatted(compact=True)

    def is_printable(self):
        """Check if data byte is printable ASCII"""
        return 32 <= self.data <= 126

    def as_char(self):
        """Return data as character (or '?' if non-printable)"""
        return chr(self.data) if self.is_printable() else '?'

    def has_errors(self):
        """Check if packet has any errors"""
        return self.parity_error or self.framing_error
