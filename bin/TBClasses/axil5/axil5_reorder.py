# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: axil5_reorder
# Purpose: Make an AXI5-Lite Subordinate BFM answer out of order across IDs
#
# Subsystem: framework

"""A reordering AXI5-Lite Subordinate (amba #104).

IHI 0022 Issue L B2.1.5: on AXI5-Lite, "reordering of responses is permitted
when requests have different IDs". The RDS-DV AXI-Lite Subordinate BFMs answer
every request after one fixed ``response_delay_cycles``, so responses always
come back in request order and a monitor that ignores the ID looks correct.

:func:`install` wraps one Subordinate interface (an ``AXIL5SlaveWrite`` or
``AXIL5SlaveRead``) so each response is held an extra number of cycles chosen
by the request's ID before the BFM's own response path runs. Give later IDs
shorter holds and the responses return in reverse. The response itself --
data, RESP, the reflected BID/RID -- is still the BFM's; only its timing
moves. Nothing here touches the DV framework.

Caveat for the Manager side: the AXI-Lite Manager BFMs hand responses to
waiting callers in arrival order, not by ID, so behind a reordering
Subordinate a caller can be handed another transaction's response. A test
using this checks the monitor and the bus, not the per-call return value.
"""

from cocotb.triggers import RisingEdge


class AXIL5ReorderingSubordinate:
    """Per-ID extra response latency on one AXI-Lite Subordinate BFM."""

    def __init__(self, iface, clock, log):
        self.iface = iface
        self.clock = clock
        self.log = log
        self.hold_cycles = {}       # request ID -> extra cycles before responding
        self.responded = []         # request IDs, in the order their response path ran

    def hold(self, mapping):
        """Set the per-ID extra latency; IDs not named get none."""
        self.hold_cycles = dict(mapping)

    async def _hold(self, req):
        rid = int(getattr(req, 'id', 0))
        for _ in range(self.hold_cycles.get(rid, 0)):
            await RisingEdge(self.clock)
        return rid

    def _wrap(self):
        wr = getattr(self.iface, '_generate_write_response', None)
        if wr is not None:
            async def _write_response(aw_packet, w_packet):
                rid = await self._hold(aw_packet)
                self.responded.append(rid)
                await wr(aw_packet, w_packet)
            self.iface._generate_write_response = _write_response
        rd = getattr(self.iface, '_generate_read_response', None)
        if rd is not None:
            async def _read_response(ar_packet):
                rid = await self._hold(ar_packet)
                self.responded.append(rid)
                await rd(ar_packet)
            self.iface._generate_read_response = _read_response
        if wr is None and rd is None:
            raise RuntimeError(
                f"{type(self.iface).__name__} has no _generate_write_response or "
                "_generate_read_response; cannot reorder its responses")


def install(iface, clock, log):
    """Wrap ``iface`` (an AXI-Lite Subordinate interface). Returns the wrapper."""
    sub = AXIL5ReorderingSubordinate(iface, clock, log)
    sub._wrap()
    log.info(f"AXIL5 reordering Subordinate installed on {type(iface).__name__}")
    return sub
