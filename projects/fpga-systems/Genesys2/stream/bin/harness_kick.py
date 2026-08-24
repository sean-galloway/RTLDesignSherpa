# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
"""Multi-channel kick — single source of truth.

Stage each channel's descriptor address in STREAM's CHx_CTRL_{LOW,HIGH}, then
issue ONE write to KICK_ENABLE with a channel bitmask. Every selected channel
launches on the same aclk cycle, so a multi-channel run measures real
concurrency rather than a staggered start.

History, because the name of this module still says "harness": the launch used
to live in the char harness. harness_csr.sv shadowed descriptor addresses in
CH_KICK_ADDR (0xB0..0xD0, split around a KICK_GO slot at 0xC0) and pulsed
STREAM's i_kick_burst_* ports. That existed only because the alternative was
apb4todescr's LOW/HIGH APB handshake -- one full UART round trip per channel,
milliseconds apart at 115200 baud. STREAM now owns both halves: the addresses
are ordinary stored registers and KICK_ENABLE is the launch, so the harness
carries no kick state and those ports are gone.

Other host scripts import batch_kick from here rather than re-implementing
stage-then-launch.
"""

from __future__ import annotations

from typing import Mapping, Protocol

from harness_addrs import H, HARNESS_CSR_BASE   # noqa: F401  (HARNESS_CSR_BASE re-exported)
from stream_addrs import A                     # by-name STREAM APB resolution


def kick_addr_csr(ch: int) -> int:
    """Absolute address of a channel's staged descriptor-address register (LOW word).

    Now a STREAM register (CHx_CTRL_LOW), not a harness shadow: the launch moved
    inside STREAM. Kept so callers that only wanted the address keep working.
    """
    if not 0 <= ch < 8:
        raise ValueError(f"channel {ch} out of range 0..7")
    return A(f"CH{ch}_CTRL_LOW")


class _Bridge(Protocol):
    """Minimal AXIL write interface the batch kick needs."""
    def write(self, addr: int, data: int) -> bool: ...


def batch_kick(bridge: _Bridge, kicks: Mapping[int, int]) -> int:
    """Stage every channel's descriptor address, then launch them in one write.

    `kicks` maps {channel: descriptor_address}. Writes each channel's
    CHx_CTRL_{LOW,HIGH}, then a single STREAM KICK_ENABLE with the combined
    bitmask, so every selected channel starts on the SAME clock edge. Returns
    the mask written.

    This used to go through the harness KICK_GO CSR, which shadowed descriptor
    addresses in harness_csr and pulsed STREAM's i_kick_burst_* ports. That
    existed only because kicking through APB cost one UART transaction per
    channel. STREAM now owns both halves, so the harness no longer carries kick
    state and the ports are gone.

    Programs the LOW 32 bits only. CHx_CTRL_HIGH is a separate stored register
    that resets to 0 and nothing writes it, so on a 32-bit-addressed build the
    HIGH write is a wasted bus transaction per channel -- and over UART those
    are exactly what the single-shot launch exists to avoid. A caller needing
    >4 GB descriptor addresses must stage CHx_CTRL_HIGH itself before calling.
    """
    if not kicks:
        return 0
    mask = 0
    for ch, desc_addr in kicks.items():
        if not bridge.write(A(f"CH{ch}_CTRL_LOW"), desc_addr & 0xFFFF_FFFF):
            raise IOError(f"staged-addr LOW write failed for channel {ch}")
        mask |= (1 << ch)
    if not bridge.write(A("KICK_ENABLE"), mask):
        raise IOError(f"KICK_ENABLE write failed (mask={mask:#x})")
    return mask
