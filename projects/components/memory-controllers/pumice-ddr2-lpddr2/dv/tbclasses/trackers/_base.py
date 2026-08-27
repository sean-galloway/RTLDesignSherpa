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
from typing import Dict, List, Optional

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


def tracker_clock(dut, log=None):
    """Resolve a FUB's clock handle by NAME, tolerating the rearchitecture.

    The pre-rearchitecture FUBs used `mc_clk`; the rearchitected ones use
    `aclk` (and the DFI-domain blocks `dfi_clk`). Trackers must not
    hard-code either -- a tracker that raises AttributeError takes the
    whole TEST down with it, which is exactly backwards for passive
    instrumentation (found 2026-08-27: every tracker hardcoded mc_clk and
    none had been run against the rearchitected core).
    """
    for name in ('aclk', 'mc_clk', 'clk', 'dfi_clk'):
        h = getattr(dut, name, None)
        if h is not None:
            return h
    if log is not None:
        log.warning("tracker_clock: no clock on %s", getattr(dut, '_name', dut))
    return None


def guard_run(coro_fn, short_name: str, log=None):
    """Wrap a tracker's run() so a signal miss disables THAT tracker
    instead of failing the test. Passive instrumentation must never be
    able to turn a green run red."""
    async def _wrapped():
        try:
            await coro_fn()
        except Exception as e:                      # noqa: BLE001
            msg = f"[tracker {short_name}] disabled after error: {e}"
            if log is not None:
                log.warning(msg)
            else:
                print(msg, file=sys.stderr)
    return _wrapped


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
                  autostart: bool = True,
                  scope_path: Optional[str] = None,
                  scope_paths: Optional[Dict[str, str]] = None) -> dict:
    """Convenience: instantiate every tracker on `dut` with consistent
    output_dir + log, optionally start their run() coroutines.

    Returns a dict keyed by short-name: {'sched': SchedulerTracker(...), ...}.

    Each tracker writes `<output_dir>/<short>.out` at end of sim
    (default output_dir is the cwd, which for cocotb_test runs is the
    simulation's sim_build/ directory).

    Pass `autostart=False` if you want to start tasks yourself (e.g.,
    to defer until after reset). With `autostart=True` (default), the
    function calls `cocotb.start_soon(t.run())` for each tracker.

    Two scoping modes:

    1. ``scope_path`` (single string): walk every tracker to the same
       sub-scope. Useful when the dut handle is the TB top and all
       tracked FUBs live under one wrapper (e.g. ``"u_dut"``).

    2. ``scope_paths`` (dict of short-name -> path): per-tracker scope.
       This is REQUIRED at integration TB scopes because each tracker
       actually monitors a different sub-module. Example for the
       core TB env. CURRENT hierarchy (updated 2026-08-27 for the
       rearchitected core: ``pumice_core`` instantiates ``u_sched``
       (pumice_mem_cmd_scheduler), ``u_ifc`` (pumice_axi4_ifc) and
       ``u_dfi`` (pumice_dfi_layer)):

           wire_trackers(dut, scope_paths={
               "sched":   "u_core.u_sched.u_arbiter",
               "btmr":    "u_core.u_sched.u_bank_timers",
               "refr":    "u_core.u_sched.u_refresh",
               "pgpol":   "u_core.u_sched.u_page_policy",
               "init":    "u_core.u_sched.u_init",
               "camrd":   "u_core.u_ifc.u_rd_cam",
               "camwr":   "u_core.u_ifc.u_wr_cam",
               "dficmd":  "u_core.u_dfi.u_cmd",
               "wrbeat":  "u_core.u_dfi.u_wr",
               "rdalign": "u_core.u_dfi.u_rd",
           })

       (Prefix each path with ``u_dut.`` at the pumice_top TB scope.)
       ``pdn`` is only present in builds that instantiate
       ``powerdown_ctrl``; it is skipped when the handle does not
       resolve.

       In per-FUB tests (where ``dut`` IS the specific FUB), omit
       both arguments — the trackers work as-is, just like before.
    """
    # Walk the hierarchy if a scope_path is provided. Each step is a
    # getattr; if any link is missing we fall back to dut and let the
    # individual signal-misses surface naturally (the trackers tolerate
    # missing signals via is_high / safe_int returning 0/False).
    scope = dut
    if scope_path:
        for part in scope_path.split("."):
            part = part.strip()
            if not part:
                continue
            nxt = getattr(scope, part, None)
            if nxt is None:
                if log is not None:
                    log.warning(
                        "wire_trackers: scope_path %r failed at %r — "
                        "falling back to dut top level",
                        scope_path, part)
                scope = dut
                break
            scope = nxt

    # Local imports to avoid circular deps.
    from .scheduler_tracker         import SchedulerTracker
    from .refresh_tracker           import RefreshTracker
    from .bank_timers_tracker       import BankTimersTracker
    from .page_policy_tracker        import PagePolicyTracker
    from .cam_tracker                import CamTracker
    from .dfi_cmd_formatter_tracker import DfiCmdFormatterTracker
    from .powerdown_tracker         import PowerdownTracker
    from .init_sequencer_tracker    import InitSequencerTracker
    from .wr_beat_sequencer_tracker import WrBeatSequencerTracker
    from .rd_cl_aligner_tracker     import RdClAlignerTracker

    # Per-tracker scope resolution. If scope_paths is given, each short
    # name maps to its own sub-scope walked from `dut`. Fall back to the
    # shared `scope` (which itself may have been walked from dut via
    # scope_path) when a name isn't listed.
    def _resolve(short_name: str):
        if scope_paths and short_name in scope_paths:
            sp = scope_paths[short_name]
            cur = dut
            for part in sp.split("."):
                part = part.strip()
                if not part:
                    continue
                nxt = getattr(cur, part, None)
                if nxt is None:
                    if log is not None:
                        log.warning(
                            "wire_trackers[%s]: scope %r failed at %r — "
                            "falling back to shared scope",
                            short_name, sp, part)
                    return scope
                cur = nxt
            return cur
        return scope

    common = dict(output_dir=output_dir, log=log)
    trackers = {
        'sched':   SchedulerTracker(_resolve('sched'),      **common),
        'refr':    RefreshTracker(_resolve('refr'),          **common),
        'btmr':    BankTimersTracker(_resolve('btmr'),       num_ranks=num_ranks, num_banks=num_banks, **common),
        'pgpol':   PagePolicyTracker(_resolve('pgpol'),      num_banks=num_banks, **common),
        'camrd':   CamTracker(_resolve('camrd'), kind='rd',  **common),
        'camwr':   CamTracker(_resolve('camwr'), kind='wr',  **common),
        'dficmd':  DfiCmdFormatterTracker(_resolve('dficmd'), **common),
        'init':    InitSequencerTracker(_resolve('init'),    **common),
        'wrbeat':  WrBeatSequencerTracker(_resolve('wrbeat'), **common),
        'rdalign': RdClAlignerTracker(_resolve('rdalign'),   **common),
    }
    # powerdown_ctrl is optional in the rearchitected core -- only wire
    # its tracker when the instance actually resolves.
    _pdn_scope = _resolve('pdn')
    if _pdn_scope is not None and getattr(_pdn_scope, 'pdn_req_o', None) is not None:
        trackers['pdn'] = PowerdownTracker(_pdn_scope, num_ranks=num_ranks, **common)
    if autostart:
        try:
            import cocotb
            for _short, t in trackers.items():
                cocotb.start_soon(guard_run(t.run, _short, log)())
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
