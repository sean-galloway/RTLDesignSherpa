# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway
#
# Module: RefreshTracker
# Purpose: Passive monitor for the refresh_ctrl FUB's bus activity and
#          JEDEC tREFI compliance.

"""
Passive tracker for the `refresh_ctrl` FUB.

Observes (does not drive) refresh_ctrl's outputs every clock cycle and
records refresh request / grant / postpone events. Provides JEDEC
tREFI compliance checks and stats:

  * tREFI compliance — request edges should fire every t_refi_i cycles
  * Postponed-refresh accumulator — JEDEC max 8 (must never exceed)
  * Refresh-to-grant latency — how long the scheduler held off
  * Refresh interval histogram — for power / thermal analysis

Signals observed:

  refresh_ctrl outputs:
    refresh_req_o          — 1 while a refresh is pending
    pending_refreshes_o    — postponed-refresh counter (JEDEC max 8)

  scheduler refresh handshake (optional — wire if the TB exposes it):
    refresh_grant_o        — pulse when REF is actually issued

  config:
    t_refi_i               — programmed tREFI interval (cycles)

Usage:
    tracker = RefreshTracker(dut, t_refi_signal='t_refi_i')
    cocotb.start_soon(tracker.run())
    ...
    assert tracker.max_pending_refreshes() <= 8, "JEDEC violation"
"""

from __future__ import annotations

from collections import deque
from dataclasses import dataclass
from typing import Deque, Dict, List, Optional

import cocotb
from cocotb.triggers import RisingEdge, Timer


_NBA_SETTLE_PS = 1
_JEDEC_MAX_POSTPONED = 8


@dataclass
class RefreshReqEdge:
    """A 0→1 transition on refresh_req_o (new refresh request)."""
    sim_time_ns: float
    cycle: int
    pending: int                  # postponed count at this moment


@dataclass
class RefreshGrant:
    """A pulse on refresh_grant_o (scheduler issued REF)."""
    sim_time_ns: float
    cycle: int
    pending_at_grant: int


@dataclass
class PendingSample:
    """A snapshot of pending_refreshes_o whenever it changes."""
    sim_time_ns: float
    cycle: int
    pending: int


class RefreshTracker:
    """Background tracker for refresh_ctrl. Call
    `cocotb.start_soon(tracker.run())` after the clock is up; query the
    event queues + statistics methods after the simulation completes."""

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

        # Event queues
        self.req_edges:      Deque[RefreshReqEdge] = deque()
        self.grants:         Deque[RefreshGrant]   = deque()
        self.pending_samples:Deque[PendingSample]  = deque()

        # State
        self._last_req     = 0
        self._last_pending = 0

    # ---------------- main coroutine ----------------

    async def run(self) -> None:
        while True:
            await RisingEdge(self.dut.mc_clk)
            await Timer(_NBA_SETTLE_PS, units='ps')
            self._cycle += 1

            req     = _safe_int(self.dut, self._sig_req,     0)
            pending = _safe_int(self.dut, self._sig_pending, 0)

            t = _sim_time_ns()

            # 0→1 edge on req → new refresh request
            if req and not self._last_req:
                self.req_edges.append(RefreshReqEdge(
                    sim_time_ns=t, cycle=self._cycle, pending=pending,
                ))
                if self.log:
                    self.log.debug(
                        f"RefreshTracker: req_edge cycle={self._cycle} pending={pending}")

            # Grant pulse
            if self._sig_grant and _is_high(self.dut, self._sig_grant):
                self.grants.append(RefreshGrant(
                    sim_time_ns=t, cycle=self._cycle,
                    pending_at_grant=pending,
                ))
                if self.log:
                    self.log.debug(
                        f"RefreshTracker: grant cycle={self._cycle} pending={pending}")

            # Sample pending when it changes
            if pending != self._last_pending:
                self.pending_samples.append(PendingSample(
                    sim_time_ns=t, cycle=self._cycle, pending=pending,
                ))

            self._last_req     = req
            self._last_pending = pending

    # ---------------- compliance checks ----------------

    def max_pending_refreshes(self) -> int:
        """Highest postponed-refresh count seen. Must be ≤ 8 per JEDEC."""
        if not self.pending_samples:
            return self._last_pending
        return max(s.pending for s in self.pending_samples)

    def jedec_postpone_violation(self) -> bool:
        """True if pending_refreshes ever exceeded JEDEC's max of 8."""
        return self.max_pending_refreshes() > _JEDEC_MAX_POSTPONED

    def refresh_intervals(self) -> List[int]:
        """List of cycle intervals between consecutive grant events. For
        JEDEC tREFI compliance, the long-term average should ≈ t_refi_i
        (the controller is allowed to deviate within the postponed-8
        window)."""
        cycles = [g.cycle for g in self.grants]
        return [b - a for a, b in zip(cycles, cycles[1:])]

    def avg_refresh_interval(self) -> Optional[float]:
        intervals = self.refresh_intervals()
        if not intervals:
            return None
        return sum(intervals) / len(intervals)

    def request_to_grant_latency(self) -> List[int]:
        """For each request-edge, latency to the next grant (in cycles).
        Long latencies suggest the scheduler is starving refresh; this is
        also implicitly a tREFI risk if it pushes postponed_count high."""
        latencies: List[int] = []
        grant_iter = iter(self.grants)
        try:
            current_grant = next(grant_iter)
        except StopIteration:
            return latencies
        for req in self.req_edges:
            while current_grant.cycle < req.cycle:
                try:
                    current_grant = next(grant_iter)
                except StopIteration:
                    return latencies
            latencies.append(current_grant.cycle - req.cycle)
        return latencies

    # ---------------- statistics ----------------

    def stats(self) -> Dict[str, object]:
        intervals = self.refresh_intervals()
        latencies = self.request_to_grant_latency()
        t_refi = _safe_int(self.dut, self._sig_t_refi, 0)
        return {
            'total_req_edges':           len(self.req_edges),
            'total_grants':              len(self.grants),
            'max_pending_refreshes':     self.max_pending_refreshes(),
            'jedec_postpone_violation':  self.jedec_postpone_violation(),
            'avg_refresh_interval':      self.avg_refresh_interval(),
            'min_refresh_interval':      min(intervals) if intervals else None,
            'max_refresh_interval':      max(intervals) if intervals else None,
            'avg_req_to_grant_lat':      (sum(latencies) / len(latencies))
                                          if latencies else None,
            'max_req_to_grant_lat':      max(latencies) if latencies else None,
            'configured_t_refi':         t_refi,
            'cycles_observed':           self._cycle,
        }


# ---------------------------------------------------------------------------
# Helpers (shared with scheduler_tracker's pattern)
# ---------------------------------------------------------------------------

def _is_high(dut, name: str) -> bool:
    sig = getattr(dut, name, None)
    if sig is None:
        return False
    try:
        return int(sig.value) != 0
    except Exception:
        return False


def _safe_int(dut, name: str, default: int) -> int:
    sig = getattr(dut, name, None)
    if sig is None:
        return default
    try:
        return int(sig.value)
    except Exception:
        return default


def _sim_time_ns() -> float:
    try:
        from cocotb.utils import get_sim_time
        return get_sim_time('ns')
    except Exception:
        return 0.0
