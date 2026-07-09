# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
"""Harness kick-burst fast path — single source of truth.

The char harness (`harness_csr.sv`) exposes STREAM's `i_kick_burst_mask` /
`i_kick_burst_addr` ports as CSRs so the host can fire N channel kicks
back-to-back in one aclk cycle instead of serializing on the slow
`apbtodescr` LOW/HIGH APB handshake (each of which is a full UART round trip).

Programming sequence (see harness_csr.sv address map, 0xB0..0xD0):
    1. Write CH_KICK_ADDR[ch] = descriptor address, for each channel to kick.
    2. Write KICK_GO = bitmask of those channels. That single write pulses the
       in-hardware kick line for every set bit for exactly one cycle.

CSR layout note: KICK_GO sits at 0xC0, in the *middle* of the kick-address slot
range, so the per-channel slots split into two banks. A naive `base + 4*ch`
stride lands ch=4 on 0xC0 and writes the address into KICK_GO — firing a
spurious kick and never delivering channels >= 4. Always use kick_addr_csr().

This module is the ONE place these offsets live; other host scripts import
from here rather than re-declaring them.
"""

from __future__ import annotations

from typing import Mapping, Protocol

from harness_addrs import H, HARNESS_CSR_BASE   # by-name harness CSR resolution (no hardcoded offsets)

# Back-compat re-export (resolved BY NAME now, not a hardcoded offset).
CSR_KICK_GO = H("KICK_GO")


def kick_addr_csr(ch: int) -> int:
    """Absolute CSR address of the per-channel kick-address shadow register.

    Resolved BY NAME from harness_csr_regmap.py (CH{ch}_KICK_ADDR). The 8-channel
    layout splits around the 0xC0 KICK_GO slot (ch 0..3 -> 0xB0..0xBC,
    ch 4..7 -> 0xC4..0xD0); that split now lives in the regmap, not here, so a
    map change follows automatically.
    """
    if not 0 <= ch < 8:
        raise ValueError(f"channel {ch} out of range 0..7")
    return H(f"CH{ch}_KICK_ADDR")


class _Bridge(Protocol):
    """Minimal AXIL write interface the batch kick needs."""
    def write(self, addr: int, data: int) -> bool: ...


def batch_kick(bridge: _Bridge, kicks: Mapping[int, int]) -> int:
    """Program address registers, then write the go bit — N kicks, one cycle.

    `kicks` maps {channel: descriptor_address}. Loads every CH_KICK_ADDR shadow
    register, then issues a single KICK_GO with the combined channel bitmask, so
    all selected channels are kicked back-to-back within one aclk cycle. Returns
    the mask written to KICK_GO.

    The descriptor address is truncated to 32 bits: the kick-burst port is
    ADDR_WIDTH-wide (32 in current builds) and the shadow register is 32 bits —
    unlike the apbtodescr path there is no separate HIGH word to program.
    """
    if not kicks:
        return 0
    mask = 0
    for ch, desc_addr in kicks.items():
        if not bridge.write(kick_addr_csr(ch), desc_addr & 0xFFFF_FFFF):
            raise IOError(f"kick-addr write failed for channel {ch}")
        mask |= (1 << ch)
    if not bridge.write(H("KICK_GO"), mask):
        raise IOError(f"KICK_GO write failed (mask={mask:#x})")
    return mask
