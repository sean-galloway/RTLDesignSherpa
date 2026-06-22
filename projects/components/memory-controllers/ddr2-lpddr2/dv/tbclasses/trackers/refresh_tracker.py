# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway
#
# Module: RefreshTracker
# Purpose: Passive monitor for the refresh_ctrl FUB's bus activity and
#          JEDEC tREFI compliance.

"""
Passive tracker for the `refresh_ctrl` FUB.

## Signals → events table

| Signal observed             | Event emitted    | Notes                              |
|-----------------------------|------------------|------------------------------------|
| `refresh_req_o` (0→1 edge)  | `REQ_EDGE`       | A new postponed-refresh request    |
| `refresh_grant_o` pulse     | `GRANT`          | Scheduler issued the REF           |
| `pending_refreshes_o` change| `PENDING_<n>`    | Postponed-refresh counter snapshot |

## Compliance

* `jedec_postpone_violation()` — fails if pending ever exceeds 8 (JEDEC max)
* `refresh_intervals()` — cycle interval between consecutive grants
* `request_to_grant_latency()` — how long the scheduler held off each request
"""

from __future__ import annotations

from collections import deque
from typing import Deque, Dict, List, Optional

import cocotb
from cocotb.triggers import RisingEdge, Timer

from ._base import TrackerEvent, is_high, safe_int, _sim_time_ns


_NBA_SETTLE_PS = 1
_TRACKER_NAME  = "refr"
_JEDEC_MAX_POSTPONED = 8


class RefreshTracker:
    """Background tracker for refresh_ctrl."""

    def __init__(self, dut, log=None,
                 refresh_req_signal: str = 'refresh_req_o',
                 pending_signal:     str = 'pending_refreshes_o',
                 refresh_grant_signal: Optional[str] = 'refresh_grant_o',
                 t_refi_signal:      str = 't_refi_i'):
        self.dut = dut
        self.log = log
        self._cycle = 0
        self._sig_req     = refresh_req_signal
        self._sig_pending = pending_signal
        self._sig_grant   = refresh_grant_signal
        self._sig_t_refi  = t_refi_signal
        self._last_req     = 0
        self._last_pending = 0
        self.events: Deque[TrackerEvent] = deque()

    async def run(self) -> None:
        while True:
            await RisingEdge(self.dut.mc_clk)
            await Timer(_NBA_SETTLE_PS, units='ps')
            self._cycle += 1

            req     = safe_int(self.dut, self._sig_req,     0)
            pending = safe_int(self.dut, self._sig_pending, 0)

            if req and not self._last_req:
                self._push("REQ_EDGE", data=f"pending={pending}")

            if self._sig_grant and is_high(self.dut, self._sig_grant):
                self._push("GRANT", data=f"pending_at_grant={pending}")

            if pending != self._last_pending:
                self._push(f"PENDING_{pending}", data=f"prev={self._last_pending}")

            self._last_req     = req
            self._last_pending = pending

    def _push(self, event: str, **kw) -> None:
        ev = TrackerEvent(
            sim_time_ns=_sim_time_ns(), cycle=self._cycle,
            tracker=_TRACKER_NAME, event=event,
            rank=kw.get('rank', -1),
            bank=kw.get('bank', -1),
            slot=kw.get('slot', -1),
            data=kw.get('data', ""),
        )
        self.events.append(ev)
        if self.log:
            self.log.debug(ev.to_md_row())

    # ---------------- compliance ----------------

    def max_pending_refreshes(self) -> int:
        m = self._last_pending
        for ev in self.events:
            if ev.event.startswith("PENDING_"):
                try:
                    m = max(m, int(ev.event[8:]))
                except ValueError:
                    pass
        return m

    def jedec_postpone_violation(self) -> bool:
        return self.max_pending_refreshes() > _JEDEC_MAX_POSTPONED

    def refresh_intervals(self) -> List[int]:
        cycles = [ev.cycle for ev in self.events if ev.event == "GRANT"]
        return [b - a for a, b in zip(cycles, cycles[1:])]

    def avg_refresh_interval(self) -> Optional[float]:
        ints = self.refresh_intervals()
        return (sum(ints) / len(ints)) if ints else None

    def request_to_grant_latency(self) -> List[int]:
        req_cycles   = [ev.cycle for ev in self.events if ev.event == "REQ_EDGE"]
        grant_cycles = [ev.cycle for ev in self.events if ev.event == "GRANT"]
        latencies: List[int] = []
        gi = iter(grant_cycles)
        try:
            g = next(gi)
        except StopIteration:
            return latencies
        for r in req_cycles:
            while g < r:
                try:
                    g = next(gi)
                except StopIteration:
                    return latencies
            latencies.append(g - r)
        return latencies

    def stats(self) -> Dict[str, object]:
        intervals = self.refresh_intervals()
        latencies = self.request_to_grant_latency()
        req_n   = sum(1 for ev in self.events if ev.event == "REQ_EDGE")
        grant_n = sum(1 for ev in self.events if ev.event == "GRANT")
        return {
            'total_req_edges':           req_n,
            'total_grants':              grant_n,
            'max_pending_refreshes':     self.max_pending_refreshes(),
            'jedec_postpone_violation':  self.jedec_postpone_violation(),
            'avg_refresh_interval':      self.avg_refresh_interval(),
            'min_refresh_interval':      min(intervals) if intervals else None,
            'max_refresh_interval':      max(intervals) if intervals else None,
            'avg_req_to_grant_lat':      (sum(latencies)/len(latencies)) if latencies else None,
            'max_req_to_grant_lat':      max(latencies) if latencies else None,
            'configured_t_refi':         safe_int(self.dut, self._sig_t_refi, 0),
            'cycles_observed':           self._cycle,
        }
