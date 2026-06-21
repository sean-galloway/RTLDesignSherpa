# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway
#
# Module: SchedulerTracker
# Purpose: Passive monitor for the scheduler FUB's external bus activity.

"""
Passive tracker for the `scheduler` FUB.

Observes (does not drive) the scheduler's external outputs every clock
cycle and decodes them into typed event records stored in queues for
later inspection by the testbench. Useful for:

  * Replay debug — dump the issued command stream after a failure
  * Coverage  — count distribution of issued ops, banks touched, etc.
  * Compliance checks — assert tCCD / refresh / init priority hold
  * Performance — measure issue rate, idle gaps, W/R balance

Signals observed (all are scheduler outputs, no internal probes needed):

  Command channel:
    cmd_valid_o, cmd_ready_i (handshake)
    cmd_op_o, cmd_rank_o, cmd_bank_o, cmd_row_o, cmd_col_o, cmd_len_o
    cmd_wr_slot_o, cmd_rd_slot_o

  Bank-event strobes:
    evt_act_o, evt_rd_o, evt_wr_o, evt_pre_o, evt_ap_o
    evt_rank_o, evt_bank_o

  Grant pulses:
    refresh_grant_o, pdn_grant_o, mr_grant_o

  Mark-issued strobes (to CAMs):
    wr_issued_we_o, wr_issued_slot_o
    rd_issued_we_o, rd_issued_slot_o

Usage:
    tracker = SchedulerTracker(dut)
    cocotb.start_soon(tracker.run())
    ...
    # Later:
    for ev in tracker.cmd_events:
        print(ev)
    print(tracker.stats())
"""

from __future__ import annotations

from collections import Counter, deque
from dataclasses import dataclass, field
from typing import Deque, Dict, Optional

import cocotb
from cocotb.triggers import RisingEdge, Timer


_NBA_SETTLE_PS = 1


# dram_op_e mnemonics (mirrors ddr2_lpddr2_pkg).
_OP_NAMES = {
    0x0: "NOP",  0x1: "ACT",  0x2: "RD",   0x3: "RDA",
    0x4: "WR",   0x5: "WRA",  0x6: "PRE",  0x7: "PREA",
    0x8: "REF",  0x9: "REFPB",0xA: "MRS",  0xB: "ZQCS", 0xC: "ZQCL",
}


@dataclass
class CmdEvent:
    """One accepted command on the scheduler's cmd_* channel."""
    sim_time_ns: float
    cycle: int
    op:    int                 # dram_op_e value
    op_name: str
    rank:  int
    bank:  int
    row:   int
    col:   int
    length:int
    wr_slot: int
    rd_slot: int

    def __repr__(self) -> str:
        return (f"CmdEvent(t={self.sim_time_ns:.1f}ns cyc={self.cycle} "
                f"{self.op_name} r{self.rank}/b{self.bank}/row{self.row:#x}/"
                f"col{self.col:#x} len={self.length})")


@dataclass
class BankEvent:
    """A bank-event strobe (ACT/RD/WR/PRE) emitted to xbank_timers."""
    sim_time_ns: float
    cycle: int
    kind:  str                 # 'act' | 'rd' | 'wr' | 'pre'
    rank:  int
    bank:  int
    ap:    bool                # auto-precharge bit (RDA/WRA)


@dataclass
class GrantEvent:
    """A grant pulse (refresh / pdn / mr)."""
    sim_time_ns: float
    cycle: int
    kind:  str                 # 'refresh' | 'pdn' | 'mr'


@dataclass
class IssuedEvent:
    """A mark-issued strobe back to a CAM."""
    sim_time_ns: float
    cycle: int
    direction: str             # 'wr' | 'rd'
    slot:  int


class SchedulerTracker:
    """Background tracker for the scheduler. Call `cocotb.start_soon(tracker.run())`
    after the clock is up, then inspect the event queues."""

    def __init__(self, dut, log=None):
        self.dut = dut
        self.log = log
        self._cycle = 0

        # Event queues — unbounded; consumers can deque or scan.
        self.cmd_events:    Deque[CmdEvent]    = deque()
        self.bank_events:   Deque[BankEvent]   = deque()
        self.grant_events:  Deque[GrantEvent]  = deque()
        self.issued_events: Deque[IssuedEvent] = deque()

    # ---------------- main coroutine ----------------

    async def run(self) -> None:
        while True:
            await RisingEdge(self.dut.mc_clk)
            await Timer(_NBA_SETTLE_PS, units='ps')
            self._cycle += 1
            self._sample_cmd()
            self._sample_bank_events()
            self._sample_grants()
            self._sample_issued()

    # ---------------- sub-samplers ----------------

    def _sim_time_ns(self) -> float:
        try:
            from cocotb.utils import get_sim_time
            return get_sim_time('ns')
        except Exception:
            return 0.0

    def _sample_cmd(self) -> None:
        if not _is_high(self.dut, 'cmd_valid_o'):
            return
        if not _is_high(self.dut, 'cmd_ready_i'):
            return
        op = int(self.dut.cmd_op_o.value)
        ev = CmdEvent(
            sim_time_ns=self._sim_time_ns(),
            cycle=self._cycle,
            op=op,
            op_name=_OP_NAMES.get(op, f"OP_{op:#x}"),
            rank=  _safe_int(self.dut, 'cmd_rank_o', 0),
            bank=  _safe_int(self.dut, 'cmd_bank_o', 0),
            row=   _safe_int(self.dut, 'cmd_row_o',  0),
            col=   _safe_int(self.dut, 'cmd_col_o',  0),
            length=_safe_int(self.dut, 'cmd_len_o',  0),
            wr_slot=_safe_int(self.dut, 'cmd_wr_slot_o', 0),
            rd_slot=_safe_int(self.dut, 'cmd_rd_slot_o', 0),
        )
        self.cmd_events.append(ev)
        if self.log:
            self.log.debug(f"SchedulerTracker: {ev}")

    def _sample_bank_events(self) -> None:
        rank = _safe_int(self.dut, 'evt_rank_o', 0)
        bank = _safe_int(self.dut, 'evt_bank_o', 0)
        ap   = _is_high(self.dut, 'evt_ap_o')
        t    = self._sim_time_ns()
        for kind, sig in [('act', 'evt_act_o'), ('rd', 'evt_rd_o'),
                          ('wr', 'evt_wr_o'),  ('pre','evt_pre_o')]:
            if _is_high(self.dut, sig):
                self.bank_events.append(BankEvent(
                    sim_time_ns=t, cycle=self._cycle,
                    kind=kind, rank=rank, bank=bank, ap=ap,
                ))

    def _sample_grants(self) -> None:
        t = self._sim_time_ns()
        for kind, sig in [('refresh','refresh_grant_o'),
                          ('pdn',    'pdn_grant_o'),
                          ('mr',     'mr_grant_o')]:
            if _is_high(self.dut, sig):
                self.grant_events.append(GrantEvent(
                    sim_time_ns=t, cycle=self._cycle, kind=kind,
                ))

    def _sample_issued(self) -> None:
        t = self._sim_time_ns()
        if _is_high(self.dut, 'wr_issued_we_o'):
            self.issued_events.append(IssuedEvent(
                sim_time_ns=t, cycle=self._cycle, direction='wr',
                slot=_safe_int(self.dut, 'wr_issued_slot_o', 0),
            ))
        if _is_high(self.dut, 'rd_issued_we_o'):
            self.issued_events.append(IssuedEvent(
                sim_time_ns=t, cycle=self._cycle, direction='rd',
                slot=_safe_int(self.dut, 'rd_issued_slot_o', 0),
            ))

    # ---------------- statistics ----------------

    def stats(self) -> Dict[str, object]:
        """Summary statistics. Call after the simulation is done."""
        op_counts: Counter[str] = Counter(ev.op_name for ev in self.cmd_events)
        bank_event_counts: Counter[str] = Counter(ev.kind for ev in self.bank_events)
        grant_counts: Counter[str] = Counter(ev.kind for ev in self.grant_events)
        per_bank_acts: Counter[int] = Counter(
            ev.bank for ev in self.bank_events if ev.kind == 'act'
        )
        ap_count = sum(1 for ev in self.bank_events
                       if ev.kind in ('rd', 'wr') and ev.ap)
        nonap_count = sum(1 for ev in self.bank_events
                          if ev.kind in ('rd', 'wr') and not ev.ap)
        return {
            'total_cmds':         len(self.cmd_events),
            'op_counts':          dict(op_counts),
            'bank_event_counts':  dict(bank_event_counts),
            'grant_counts':       dict(grant_counts),
            'per_bank_act_counts':dict(per_bank_acts),
            'col_ops_with_ap':    ap_count,    # closed-page or HAPPY-close
            'col_ops_open_page':  nonap_count, # OPEN or HAPPY-open
            'cycles_observed':    self._cycle,
        }

    # ---------------- query helpers ----------------

    def last_cmd_of(self, op_name: str) -> Optional[CmdEvent]:
        """Return the most recent CmdEvent matching `op_name`, or None."""
        for ev in reversed(self.cmd_events):
            if ev.op_name == op_name:
                return ev
        return None

    def cmds_by_bank(self, rank: int, bank: int):
        """Filter cmd_events to a single (rank, bank)."""
        return [ev for ev in self.cmd_events
                if ev.rank == rank and ev.bank == bank]


# ---------------------------------------------------------------------------
# Low-level signal helpers — tolerate missing / X signals gracefully so the
# tracker doesn't crash a TB that only exposes a subset of ports.
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
