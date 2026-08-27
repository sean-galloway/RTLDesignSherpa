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
| `refresh_grant_o` pulse     | `GRANT`          | Scheduler issued the REF; data     |
|                             |                  | carries kind (ab/pb) + rotor bank  |
| `pending_refreshes_o` change| `PENDING_<n>`    | Postponed-refresh counter snapshot |
| `obs_pullin_credit_o` change| `CREDIT_<n>`     | Pull-in credit banked (v3)         |
| `refresh_drain_active_o` edge | `DRAIN_ON/OFF` | Burst-drain window (refresh_burst) |
| `refresh_kind_o` change     | `KIND_REFAB/PB`  | Axis-3 mode switch on the wire     |

REFpb note: the bank in a GRANT row is the controller's MIRROR of the
DEVICE's internal rotor (JESD209-2 6.6 -- the command carries no bank
address). `rotor_advances()` checks it walks 0..NUM_BANKS-1 in order,
which is what a desynchronized mirror breaks.

## Compliance

* `jedec_postpone_violation()` — fails if pending ever exceeds 8 (JEDEC max)
* `refresh_intervals()` — cycle interval between consecutive grants
* `request_to_grant_latency()` — how long the scheduler held off each request
* `rotor_advances()` — REFpb grants walk the rotor in strict order
"""

from __future__ import annotations

from collections import deque
from typing import Deque, Dict, List, Optional

import cocotb
from cocotb.triggers import RisingEdge, Timer

from ._base import TrackerEvent, is_high, safe_int, _sim_time_ns, auto_dump_register, tracker_clock


_NBA_SETTLE_PS = 1
_TRACKER_NAME  = "refr"
_JEDEC_MAX_POSTPONED = 8


class RefreshTracker:
    """Background tracker for refresh_ctrl."""
    SHORT_NAME = _TRACKER_NAME

    def __init__(self, dut, log=None,
                 output_dir: Optional[str] = None,
                 filename:   Optional[str] = None,
                 refresh_req_signal: str = 'refresh_req_o',
                 pending_signal:     str = 'pending_refreshes_o',
                 refresh_grant_signal: Optional[str] = 'refresh_grant_o',
                 t_refi_signal:      str = 't_refi_i'):
        self.dut = dut
        self._clk_h = tracker_clock(dut, log)
        self.log = log
        self._cycle = 0
        self._sig_req     = refresh_req_signal
        self._sig_pending = pending_signal
        self._sig_grant   = refresh_grant_signal
        self._sig_t_refi  = t_refi_signal
        self._last_req     = 0
        self._last_pending = 0
        self._last_credit  = 0
        self._last_drain   = 0
        self._last_kind    = None
        self._pb_banks: List[int] = []
        self.events: Deque[TrackerEvent] = deque()
        self.output_path = auto_dump_register(
            self, _TRACKER_NAME, output_dir=output_dir, filename=filename,
        )

    async def run(self) -> None:
        while True:
            await RisingEdge(self._clk_h)
            await Timer(_NBA_SETTLE_PS, units='ps')
            self._cycle += 1

            req     = safe_int(self.dut, self._sig_req,     0)
            pending = safe_int(self.dut, self._sig_pending, 0)

            if req and not self._last_req:
                self._push("REQ_EDGE", data=f"pending={pending}")

            if self._sig_grant and is_high(self.dut, self._sig_grant):
                kind = safe_int(self.dut, 'refresh_kind_o', 0)
                bank = safe_int(self.dut, 'refresh_bank_o', -1)
                if kind:
                    self._pb_banks.append(bank)
                self._push("GRANT", bank=(bank if kind else -1),
                           data=(f"kind={'REFpb' if kind else 'REFab'} "
                                 f"pending_at_grant={pending} "
                                 f"credit={safe_int(self.dut, 'obs_pullin_credit_o', 0)}"))

            if pending != self._last_pending:
                self._push(f"PENDING_{pending}", data=f"prev={self._last_pending}")

            # v3: JEDEC +-8 credit machinery + burst drain + Axis-3 mode
            credit = safe_int(self.dut, 'obs_pullin_credit_o', 0)
            if credit != self._last_credit:
                self._push(f"CREDIT_{credit}", data=f"prev={self._last_credit}")
                self._last_credit = credit

            drain = 1 if is_high(self.dut, 'refresh_drain_active_o') else 0
            if drain != self._last_drain:
                self._push("DRAIN_ON" if drain else "DRAIN_OFF",
                           data=f"pending={pending}")
                self._last_drain = drain

            kind_now = safe_int(self.dut, 'refresh_kind_o', 0)
            if kind_now != self._last_kind:
                self._push("KIND_REFPB" if kind_now else "KIND_REFAB",
                           data=f"prev={self._last_kind}")
                self._last_kind = kind_now

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

    def rotor_advances(self, num_banks: int = 8) -> bool:
        """REFpb grants must walk the device rotor in strict order. A
        desynchronized mirror (the controller precharging the wrong bank
        ahead of each refresh) shows up here as a broken sequence."""
        if len(self._pb_banks) < 2:
            return True
        for a, b in zip(self._pb_banks, self._pb_banks[1:]):
            if b != (a + 1) % num_banks:
                return False
        return True

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
            'refpb_grants':              len(self._pb_banks),
            'refpb_rotor_in_order':      self.rotor_advances(),
            'max_pullin_credit':         max(
                [self._last_credit] +
                [int(ev.event[7:]) for ev in self.events
                 if ev.event.startswith("CREDIT_")]),
            'drain_windows':             sum(1 for ev in self.events
                                             if ev.event == "DRAIN_ON"),
            'cycles_observed':           self._cycle,
        }
