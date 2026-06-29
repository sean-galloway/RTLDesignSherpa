#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway

"""Cycle-correlator across FUB trackers + DFI monitor + AXI snoops.

Loads every ``<sim_build>/*.out`` produced by:
  * the ddr2-lpddr2 dv/tbclasses/trackers/ FUB tracker atexit dumps
    (sched.out, refr.out, xbank.out, pgpred.out, dficmd.out, pdn.out,
    init.out, wrbeat.out, rdalign.out) — markdown tables with columns:
    ``| time(ns) | cycle | tracker | event | rank | bank | slot | data |``
  * the BFM-side observability streams the engine_mirror_kbN top
    scenario writes (axi_wr_snoop.out, axi_rd_snoop.out, dfi_cmd_q.out,
    dfi_wr_data.out, dfi_rd_data.out).

Then merges everything by simulation time and emits a per-cycle table.
Use ``--around <ns>`` + ``--window <ns>`` to zoom on the cycle where
the FAIL assertion fired (look for it in the scenario log).

Output is a Markdown table to stdout (or ``-o`` file) with one row per
(cycle, tracker_or_stream) and columns wide enough to skim left→right
across the controller pipeline.

Example:
  python3 cycle_correlator.py \\
      local_sim_build/test_ddr2_lpddr2_top_engine_mirror_kb4 \\
      --around 21000 --window 2000

  (look at simulation events from 20000ns to 22000ns)
"""

from __future__ import annotations

import argparse
import os
import re
import sys
from dataclasses import dataclass, field
from typing import Dict, List, Optional, Tuple


@dataclass(order=True)
class Event:
    """One event timestamped at sim_time_ns. ``stream`` names the source
    (tracker short name, or 'dfi_cmd', 'dfi_wr', 'dfi_rd', 'axi_wr',
    'axi_rd'). ``fields`` is a free-form list of columns to print."""
    sim_time_ns: float
    cycle: int = field(default=0)
    stream: str = field(default="")
    summary: str = field(default="")
    raw: str = field(default="", repr=False)


_FUB_TRACKER_NAMES = (
    "sched", "refr", "xbank", "pgpred", "dficmd", "pdn",
    "init", "wrbeat", "rdalign",
)


_MD_ROW_RE = re.compile(
    r"^\|\s*(?P<t>[0-9.]+)\s*\|\s*(?P<cyc>[0-9-]+)\s*\|"
    r"\s*(?P<tracker>[^|]+?)\s*\|(?P<rest>.*)\|\s*$"
)


def _parse_fub_tracker(path: str, stream_hint: str) -> List[Event]:
    """FUB tracker .out files are markdown tables. Skip header rows;
    parse data rows into events."""
    out: List[Event] = []
    if not os.path.exists(path):
        return out
    with open(path) as f:
        for line in f:
            line = line.rstrip("\n")
            m = _MD_ROW_RE.match(line)
            if not m:
                continue
            try:
                t_ns = float(m.group("t"))
                cyc = int(m.group("cyc"))
            except ValueError:
                continue   # header separator row
            rest = m.group("rest").strip()
            tracker = m.group("tracker").strip() or stream_hint
            out.append(Event(
                sim_time_ns=t_ns, cycle=cyc,
                stream=tracker,
                summary=rest, raw=line,
            ))
    return out


_BFM_HEADERED_RE = re.compile(r"^#")


def _parse_bfm_stream(path: str, stream: str) -> List[Event]:
    """Whitespace-separated columns; first column is t_ns where
    applicable. For axi_*_snoop the addr-keyed file has no time
    column — annotate by burst index only."""
    out: List[Event] = []
    if not os.path.exists(path):
        return out
    with open(path) as f:
        idx = 0
        for line in f:
            line = line.rstrip("\n")
            if not line or _BFM_HEADERED_RE.match(line):
                continue
            parts = line.split()
            try:
                t_ns = float(parts[0])
                rest = "  ".join(parts[1:])
            except ValueError:
                # axi_wr_snoop / axi_rd_snoop — no time column.
                t_ns = float("nan")
                rest = "  ".join(parts)
            out.append(Event(
                sim_time_ns=t_ns, cycle=int(t_ns) if t_ns == t_ns else -1,
                stream=stream, summary=rest, raw=line,
            ))
            idx += 1
    return out


def load_all(sim_build: str) -> List[Event]:
    events: List[Event] = []
    for name in _FUB_TRACKER_NAMES:
        events += _parse_fub_tracker(
            os.path.join(sim_build, f"{name}.out"), stream_hint=name)
    for name, stream in (
        ("dfi_cmd_q.out",  "dfi_cmd"),
        ("dfi_wr_data.out", "dfi_wr"),
        ("dfi_rd_data.out", "dfi_rd"),
        ("axi_wr_snoop.out", "axi_wr"),
        ("axi_rd_snoop.out", "axi_rd"),
    ):
        events += _parse_bfm_stream(os.path.join(sim_build, name), stream)
    return events


def main(argv: Optional[List[str]] = None) -> int:
    ap = argparse.ArgumentParser(
        description=__doc__,
        formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("sim_build", help="sim_build dir containing the .out files")
    ap.add_argument("--around", type=float, default=None,
                    help="center the output around this sim_time_ns")
    ap.add_argument("--window", type=float, default=2000.0,
                    help="ns window around --around (default 2000)")
    ap.add_argument("--streams", default=None,
                    help="comma-separated stream filter, e.g. "
                         "'sched,wrbeat,dfi_cmd,axi_wr'")
    ap.add_argument("-o", "--output", default=None,
                    help="write to this file instead of stdout")
    args = ap.parse_args(argv)

    events = load_all(args.sim_build)
    if not events:
        print(f"no .out files found in {args.sim_build}", file=sys.stderr)
        return 1

    if args.around is not None:
        lo = args.around - args.window / 2
        hi = args.around + args.window / 2
        events = [e for e in events
                  if (e.sim_time_ns != e.sim_time_ns)
                  or (lo <= e.sim_time_ns <= hi)]

    if args.streams:
        allow = set(s.strip() for s in args.streams.split(","))
        events = [e for e in events if e.stream in allow]

    events.sort(key=lambda e: (
        e.sim_time_ns if e.sim_time_ns == e.sim_time_ns else float("inf"),
        e.cycle, e.stream,
    ))

    out_fp = open(args.output, "w") if args.output else sys.stdout
    try:
        out_fp.write(
            f"# Cycle correlator — {args.sim_build}\n"
            f"# {len(events)} events"
            + (f" around t={args.around}ns ±{args.window/2}\n"
               if args.around is not None else "\n")
        )
        out_fp.write(
            "| sim_time_ns | cycle | stream     | event\n"
            "|------------:|------:|:-----------|:------\n"
        )
        for e in events:
            t_col = ("" if e.sim_time_ns != e.sim_time_ns
                     else f"{e.sim_time_ns:>11.1f}")
            out_fp.write(
                f"| {t_col} | {e.cycle:>5d} | {e.stream:<10s} | "
                f"{e.summary}\n"
            )
    finally:
        if args.output:
            out_fp.close()
    return 0


if __name__ == "__main__":
    sys.exit(main())
