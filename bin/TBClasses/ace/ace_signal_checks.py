# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: ace_signal_checks
# Purpose: Directed checks for the ACE address/response signals the
#          rtl/amba/ace transports carry (IHI 0022H D2.1, D2.3).
#
# Documentation: docs/markdown/rtl-amba/ace/README.md
# Subsystem: amba
#
# Author: sean galloway
# Created: 2026-10-12

"""Directed checks shared by the four ACE front-side transport TBs.

The transports are skid buffers, so every check is a reflection check: what
the BFM drives on one side must come out unchanged on the other.

- AxDOMAIN[1:0] / AxBAR[1:0] (IHI 0022H D2.1.1-2): every domain encoding and
  every barrier encoding, each in a combination Tables D3-7 / D3-8 permit.
- RRESP[3:2] = {IsShared, PassDirty} (D2.1.3, Table D3-14): all four pairs,
  constant across a burst, reach the requester unchanged.
- RACK / WACK (D2.3) on the subordinate-side transports: the manager's
  acknowledge reaches the backend, one pulse per transaction.
"""

from typing import Awaitable, Callable, List, Sequence, Tuple

from cocotb.triggers import RisingEdge

# (AxSNOOP, AxDOMAIN, AxBAR) cases. Together they cover all four domain
# encodings (Table D3-2) and all four barrier encodings (Table D3-5); each row
# is a combination Table D3-7 (read) / D3-8 (write) permits.
AR_DOMAIN_BAR_CASES: Tuple[Tuple[int, int, int], ...] = (
    (0x0, 0b00, 0b00),  # ReadNoSnoop, Non-shareable
    (0x1, 0b01, 0b00),  # ReadShared, Inner Shareable
    (0x1, 0b10, 0b10),  # ReadShared, Outer Shareable, ignoring barriers
    (0x0, 0b11, 0b00),  # ReadNoSnoop, System
    (0x0, 0b10, 0b01),  # memory barrier, Outer Shareable
    (0x0, 0b11, 0b11),  # synchronization barrier, System
)
AW_DOMAIN_BAR_CASES: Tuple[Tuple[int, int, int], ...] = (
    (0x0, 0b00, 0b00),  # WriteNoSnoop, Non-shareable
    (0x3, 0b01, 0b00),  # WriteBack, Inner Shareable
    (0x3, 0b10, 0b10),  # WriteBack, Outer Shareable, ignoring barriers
    (0x0, 0b11, 0b00),  # WriteNoSnoop, System
    (0x0, 0b10, 0b01),  # memory barrier, Outer Shareable
    (0x0, 0b11, 0b11),  # synchronization barrier, System
)

# RRESP[3:2] pairs as {IsShared, PassDirty}; all four occur for ReadShared.
COHERENCE_PAIRS: Tuple[int, ...] = (0b00, 0b01, 0b10, 0b11)


async def domain_bar_sweep(
    cases: Sequence[Tuple[int, int, int]],
    issue: Callable[[int, int, int, int], Awaitable[None]],
    drain: Callable[[], list],
    log,
) -> List[str]:
    """Issue one transaction per case and check the far side's AxDOMAIN/AxBAR.

    ``issue(index, snoop, domain, bar)`` runs one complete transaction;
    ``drain()`` returns the address packets the output monitor captured since
    the last call. Returns a list of error strings (empty on pass).
    """
    errors: List[str] = []
    drain()
    for index, (snoop, domain, bar) in enumerate(cases):
        await issue(index, snoop, domain, bar)
        packets = drain()
        if len(packets) != 1:
            errors.append(f"case {index}: expected 1 output address packet, got {len(packets)}")
            continue
        pkt = packets[0]
        got = (int(getattr(pkt, 'snoop', -1)), int(getattr(pkt, 'domain', -1)),
               int(getattr(pkt, 'bar', -1)))
        if got != (snoop, domain, bar):
            errors.append(
                f"case {index}: sent snoop/domain/bar=0x{snoop:X}/{domain:02b}/{bar:02b}, "
                f"output carried 0x{got[0]:X}/{got[1]:02b}/{got[2]:02b}")
        else:
            log.info(f"  domain/bar case {index}: snoop=0x{snoop:X} domain={domain:02b} "
                     f"bar={bar:02b} passed through")
    return errors


async def rresp_coherence_sweep(
    set_pair: Callable[[int], None],
    read: Callable[[int], Awaitable[List[int]]],
    burst_len: int,
    log,
) -> List[str]:
    """Return each {IsShared, PassDirty} pair from the responder and check the
    requester sees it on every beat of the burst.

    ``set_pair(pair)`` arms the responder; ``read(pair)`` runs one burst and
    returns the per-beat 4-bit RRESP the requester BFM observed.
    """
    errors: List[str] = []
    for pair in COHERENCE_PAIRS:
        set_pair(pair)
        resps = await read(pair)
        expected = [pair << 2] * burst_len
        if list(resps) != expected:
            errors.append(
                f"IsShared/PassDirty={pair:02b}: expected RRESP {[f'{r:04b}' for r in expected]}, "
                f"requester saw {[f'{r:04b}' for r in resps]}")
        else:
            log.info(f"  RRESP[3:2]={pair:02b} reached the requester on all {burst_len} beats")
    set_pair(0)
    return errors


class AckPassthroughProbe:
    """Samples a manager-side acknowledge and its forwarded copy every cycle.

    Start it with ``cocotb.start_soon(probe.run())`` before the traffic and
    call ``stop()`` after; ``check(expected_pulses)`` then reports whether the
    copy followed the source on every cycle and pulsed once per transaction.
    """

    def __init__(self, clock, src, dst):
        self.clock = clock
        self.src = src
        self.dst = dst
        self.mismatch_cycles = 0
        self.src_pulses = 0
        self.dst_pulses = 0
        self._running = True
        self._prev_dst = 0
        self._prev_src = 0

    async def run(self):
        while self._running:
            await RisingEdge(self.clock)
            src = int(self.src.value)
            dst = int(self.dst.value)
            if src != dst:
                self.mismatch_cycles += 1
            if src and not self._prev_src:
                self.src_pulses += 1
            if dst and not self._prev_dst:
                self.dst_pulses += 1
            self._prev_src, self._prev_dst = src, dst

    def stop(self):
        self._running = False

    def check(self, expected_pulses: int, name: str) -> List[str]:
        errors: List[str] = []
        if self.mismatch_cycles:
            errors.append(f"{name}: forwarded copy differed from the source on "
                          f"{self.mismatch_cycles} cycles")
        if self.src_pulses != expected_pulses:
            errors.append(f"{name}: manager BFM pulsed {self.src_pulses} times, "
                          f"expected {expected_pulses}")
        if self.dst_pulses != expected_pulses:
            errors.append(f"{name}: backend saw {self.dst_pulses} pulses, "
                          f"expected {expected_pulses}")
        return errors
