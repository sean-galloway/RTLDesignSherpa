# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway

"""Canonical Python mirror for ``rtl/common/shifter_lfsr_fibonacci.sv``.

Extracted from ``val/common/test_shifter_lfsr_fibonacci.py``
(``ShifterLFSRFibonacciTB.simulate_xor_lfsr``) so any TB that needs a
reference LFSR sequence imports this single source of truth. The
shifter_lfsr_fibonacci RTL is the canonical Fibonacci LFSR used by the
AXI4 pattern-gen / CRC-check engines and elsewhere; duplicating the
mirror in each TB invites drift.

Behavior matches the RTL bit-for-bit:
  - feedback = XOR of bits at (tap_position - 1) for each tap (taps are
    1-indexed, max tap == width).
  - next  = ((lfsr >> 1) | (feedback << (width - 1))) & ((1<<width)-1)
  - The first cycle after a seed-load produces ``advance(seed)``; the
    seed value itself is NOT returned. Use ``include_seed=True`` to
    prepend it (the engine pattern-gen wants this — beat 0 == seed).
"""

from __future__ import annotations

from typing import Iterable, List


def simulate_xor_lfsr(
    seed: int,
    taps: Iterable[int],
    cycles: int,
    width: int = 32,
    include_seed: bool = False,
    drop_first: bool = False,
) -> List[int]:
    """Generate LFSR values from ``seed`` under ``taps``.

    Args:
        seed:          initial LFSR state. Must be non-zero for a useful
                       sequence (zero is a fixed point).
        taps:          1-indexed tap positions (e.g. (32, 22, 2, 1) for
                       the standard 32-bit Fibonacci max-length poly).
        cycles:        number of advances to perform.
        width:         LFSR width in bits.
        include_seed:  if True, prepend the seed (no advance) before
                       the advanced values. Use when caller expects
                       ``[seed, advance#1, advance#2, …]`` such as the
                       AXI pattern-gen engine (beat 0 == seed).
        drop_first:    if True, run ``cycles+1`` advances but drop the
                       first calculated value. Matches the
                       ``ShifterLFSRFibonacciTB.simulate_xor_lfsr``
                       legacy convention where the RTL's first
                       post-load cycle is consumed by an internal
                       register delay.

    Returns:
        List of LFSR values. Length = cycles, +1 if include_seed.

    Note:
        ``include_seed`` and ``drop_first`` are mutually exclusive —
        the first is for "advance starts at output[1]", the second for
        "first advance is invisible at the RTL boundary". The engine
        pattern-gen TB uses include_seed=True; the LFSR unit-test TB
        uses drop_first=True.
    """
    if include_seed and drop_first:
        raise ValueError("include_seed and drop_first are mutually exclusive")

    mask = (1 << width) - 1
    lfsr = seed & mask
    tap_mask = 0
    for t in taps:
        if 0 < t <= width:
            tap_mask |= 1 << (t - 1)

    n_steps = cycles + (1 if drop_first else 0)
    raw: List[int] = []
    for _ in range(n_steps):
        tapped = lfsr & tap_mask
        feedback = 0
        for i in range(width):
            if (tapped >> i) & 1:
                feedback ^= 1
        lfsr = ((lfsr >> 1) | (feedback << (width - 1))) & mask
        raw.append(lfsr)

    if drop_first:
        return raw[1:]
    if include_seed:
        return [seed & mask] + raw
    return raw
