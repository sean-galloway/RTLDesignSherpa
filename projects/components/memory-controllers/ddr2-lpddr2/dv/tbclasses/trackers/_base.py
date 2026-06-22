# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway
#
# Module: tracker base
# Purpose: Shared dataclass / formatting / helpers for all FUB trackers.

"""
Shared base for FUB trackers.

Every tracker event implements `to_md_row()` which returns ONE markdown
table row with a fixed column layout. This means you can `dump_md()`
events from any tracker, concatenate them, and the result is a single
grep-friendly markdown table.

## Column layout

| time(ns)  | cycle | tracker | event | rank | bank | slot | data |
|-----------|-------|---------|-------|------|------|------|------|
| 12345.0   | 1234  | sched   | ACT   | r0   | b3   | -    | row=0x100 col=0x40 len=8 |

Each tracker decides its `tracker` short-name and its `event` mnemonic
column. Empty rank/bank/slot are rendered as `-`.

## Grep examples

After dumping every tracker's events to a single log:

```
grep '| sched   |' log.md       # all scheduler events
grep '| ACT  '   log.md         # all ACT events from any tracker
grep '| r0 *| b3 ' log.md       # everything touching rank 0 bank 3
grep '| pgpred  | open' log.md  # page predictor 0→1 transitions
```
"""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import List, Optional

try:
    from cocotb.utils import get_sim_time
    def _sim_time_ns() -> float:
        return get_sim_time('ns')
except Exception:
    def _sim_time_ns() -> float:
        return 0.0


# Fixed column widths so rows align even when grouped from many trackers.
_COL_TIME    = 10
_COL_CYCLE   = 6
_COL_TRACKER = 8
_COL_EVENT   = 14
_COL_RANK    = 4
_COL_BANK    = 4
_COL_SLOT    = 5


@dataclass
class TrackerEvent:
    """Base for every tracker event. Implements to_md_row() with a fixed
    column layout that makes events from different trackers stack into
    one searchable markdown table."""
    sim_time_ns: float
    cycle:       int
    tracker:     str
    event:       str
    rank:        int = -1
    bank:        int = -1
    slot:        int = -1
    data:        str = ""

    def to_md_row(self) -> str:
        r = f"r{self.rank}" if self.rank >= 0 else "-"
        b = f"b{self.bank}" if self.bank >= 0 else "-"
        s = f"s{self.slot}" if self.slot >= 0 else "-"
        return (f"| {self.sim_time_ns:>{_COL_TIME}.1f} "
                f"| {self.cycle:>{_COL_CYCLE}d} "
                f"| {self.tracker:<{_COL_TRACKER}s} "
                f"| {self.event:<{_COL_EVENT}s} "
                f"| {r:<{_COL_RANK}s} "
                f"| {b:<{_COL_BANK}s} "
                f"| {s:<{_COL_SLOT}s} "
                f"| {self.data} |")


def md_header() -> str:
    """Markdown table header. Emit once at the top of a dump file before
    concatenating tracker rows."""
    return (
        f"| {'time(ns)':>{_COL_TIME}s} "
        f"| {'cycle':>{_COL_CYCLE}s} "
        f"| {'tracker':<{_COL_TRACKER}s} "
        f"| {'event':<{_COL_EVENT}s} "
        f"| {'rank':<{_COL_RANK}s} "
        f"| {'bank':<{_COL_BANK}s} "
        f"| {'slot':<{_COL_SLOT}s} "
        f"| data |\n"
        f"| {'-'*_COL_TIME} "
        f"| {'-'*_COL_CYCLE} "
        f"| {'-'*_COL_TRACKER} "
        f"| {'-'*_COL_EVENT} "
        f"| {'-'*_COL_RANK} "
        f"| {'-'*_COL_BANK} "
        f"| {'-'*_COL_SLOT} "
        f"| ---- |"
    )


def dump_md_unified(trackers: List["object"], file_path: str) -> None:
    """Merge events from every tracker (each must have a `events` deque
    of TrackerEvent), sort by (cycle, sim_time_ns), and write a single
    markdown table to `file_path`."""
    all_events: List[TrackerEvent] = []
    for t in trackers:
        ev_iter = getattr(t, 'events', None)
        if ev_iter is None:
            continue
        for ev in ev_iter:
            if isinstance(ev, TrackerEvent):
                all_events.append(ev)
    all_events.sort(key=lambda e: (e.cycle, e.sim_time_ns))
    with open(file_path, 'w') as f:
        f.write(md_header() + "\n")
        for ev in all_events:
            f.write(ev.to_md_row() + "\n")


# ---------------------------------------------------------------------------
# Signal helpers — tolerate missing / X signals so a tracker doesn't crash
# a TB that only exposes a subset of ports.
# ---------------------------------------------------------------------------

def is_high(dut, name: str) -> bool:
    sig = getattr(dut, name, None)
    if sig is None:
        return False
    try:
        return int(sig.value) != 0
    except Exception:
        return False


def safe_int(dut, name: str, default: int = 0) -> int:
    sig = getattr(dut, name, None)
    if sig is None:
        return default
    try:
        return int(sig.value)
    except Exception:
        return default
