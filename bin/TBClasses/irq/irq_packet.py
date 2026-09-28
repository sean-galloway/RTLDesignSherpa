# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: IRQPacket
# Purpose: One observed transition on an interrupt line
#
# Created: 2026-09-28

"""Interrupt-line transition packet."""

from dataclasses import dataclass
from typing import Optional


@dataclass
class IRQPacket:
    """A single observed edge on an interrupt line.

    One packet per CHANGED BIT, not per sample: a vector line that asserts two
    bits in the same cycle produces two packets, so a test can count events per
    line without unpacking bit masks itself.

    Attributes:
        time_ns:  simulation time of the sampling edge, in ns
        count:    monotonic index within the monitor that produced it
        name:     the interrupt line's signal name, e.g. 'pit_timer_irq'
        index:    bit index for a vector line; None for a scalar line
        event:    'assert' or 'deassert'
        value:    the WHOLE signal's value at the sampling edge. Kept because
                  the interesting bugs in an OR fabric are about coincidence --
                  "which other bits were also high when this one asserted" is
                  not recoverable from a per-bit event stream alone.
    """

    time_ns: float = 0.0
    count: int = 0
    name: str = ""
    index: Optional[int] = None
    event: str = "assert"
    value: int = 0

    @property
    def line(self) -> str:
        """Human label for this line: 'name' or 'name[index]'."""
        return self.name if self.index is None else f"{self.name}[{self.index}]"

    def __str__(self) -> str:
        return f"{self.line} {self.event} @ {self.time_ns}ns (vec=0x{self.value:X})"
