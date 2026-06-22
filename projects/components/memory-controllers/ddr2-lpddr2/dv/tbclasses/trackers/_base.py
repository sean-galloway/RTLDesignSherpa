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

import atexit
import os
import sys
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
# Auto-dump on simulation end.
#
# Every tracker calls auto_dump_register() in its __init__. The handler
# writes the tracker's events as a markdown table to <output_dir>/<short>.out
# when the Python interpreter exits — which for cocotb_test happens at the
# end of each pytest-spawned simulation subprocess, so every test gets its
# own .out files in its sim_build/ directory.
# ---------------------------------------------------------------------------

# Track registered (short_name, output_dir) pairs so a second instance with
# the same short_name doesn't double-register.
_REGISTERED: set = set()


def auto_dump_register(tracker, short_name: str,
                       output_dir: Optional[str] = None,
                       filename:   Optional[str] = None) -> str:
    """Register an atexit handler that writes `tracker.events` as a
    markdown table.

    The output path is:
      * `filename` if given, OR
      * `<output_dir>/<short_name>.out` if output_dir given, OR
      * `<cwd>/<short_name>.out` (cwd is the cocotb simulation dir).

    Returns the resolved path.
    """
    if filename is None:
        out_dir = output_dir or os.getcwd()
        try:
            os.makedirs(out_dir, exist_ok=True)
        except Exception:
            pass
        filename = os.path.join(out_dir, f"{short_name}.out")

    # De-dup: if the same (short_name, output dir) was already registered
    # for THIS tracker, skip. Different instances with same short_name in
    # the same dir would overwrite each other; this is intentional and
    # avoids double atexit handlers.
    key = (short_name, os.path.dirname(filename))
    if key in _REGISTERED:
        return filename
    _REGISTERED.add(key)

    def _do_dump() -> None:
        try:
            with open(filename, 'w') as f:
                f.write(md_header() + "\n")
                for ev in getattr(tracker, 'events', []):
                    if isinstance(ev, TrackerEvent):
                        f.write(ev.to_md_row() + "\n")
        except Exception as e:
            print(f"[tracker {short_name}] dump to {filename} failed: {e}",
                  file=sys.stderr)

    atexit.register(_do_dump)
    return filename


def wire_trackers(dut, *, output_dir: Optional[str] = None,
                  log=None, num_ranks: int = 1, num_banks: int = 8,
                  autostart: bool = True) -> dict:
    """Convenience: instantiate every tracker on `dut` with consistent
    output_dir + log, optionally start their run() coroutines.

    Returns a dict keyed by short-name: {'sched': SchedulerTracker(...), ...}.

    Each tracker writes `<output_dir>/<short>.out` at end of sim
    (default output_dir is the cwd, which for cocotb_test runs is the
    simulation's sim_build/ directory).

    Pass `autostart=False` if you want to start tasks yourself (e.g.,
    to defer until after reset). With `autostart=True` (default), the
    function calls `cocotb.start_soon(t.run())` for each tracker.
    """
    # Local imports to avoid circular deps.
    from .scheduler_tracker         import SchedulerTracker
    from .refresh_tracker           import RefreshTracker
    from .xbank_timers_tracker      import XBankTimersTracker
    from .page_predictor_tracker    import PagePredictorTracker
    from .dfi_cmd_formatter_tracker import DfiCmdFormatterTracker
    from .powerdown_tracker         import PowerdownTracker
    from .init_sequencer_tracker    import InitSequencerTracker
    from .wr_beat_sequencer_tracker import WrBeatSequencerTracker
    from .rd_cl_aligner_tracker     import RdClAlignerTracker

    common = dict(output_dir=output_dir, log=log)
    trackers = {
        'sched':   SchedulerTracker(dut, **common),
        'refr':    RefreshTracker(dut, **common),
        'xbank':   XBankTimersTracker(dut, num_ranks=num_ranks, num_banks=num_banks, **common),
        'pgpred':  PagePredictorTracker(dut, num_ranks=num_ranks, num_banks=num_banks, **common),
        'dficmd':  DfiCmdFormatterTracker(dut, **common),
        'pdn':     PowerdownTracker(dut, num_ranks=num_ranks, **common),
        'init':    InitSequencerTracker(dut, **common),
        'wrbeat':  WrBeatSequencerTracker(dut, **common),
        'rdalign': RdClAlignerTracker(dut, **common),
    }
    if autostart:
        try:
            import cocotb
            for t in trackers.values():
                cocotb.start_soon(t.run())
        except Exception as e:
            print(f"[wire_trackers] autostart failed (no cocotb?): {e}",
                  file=sys.stderr)
    return trackers


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
