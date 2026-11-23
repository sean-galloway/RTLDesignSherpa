#!/usr/bin/env python3
"""Read a proxy DRAM trace (`PERF_DRAM_TRACE`, [[cycle, kind, bank, phase], ...]) by inter-refresh segment.

Under close page every column auto-precharges, so the only explicit PREs are the plane's drain of the open
rows before a REF: a cluster of PREs marks each refresh. For each segment between refreshes the tool prints
the stream's cadence in MC cycles per column, the ACTs by DFI phase (1 = the row lane, 0 = the main slot),
the ACT -> column distance histogram and the column-gap histogram; then the gap around each refresh (last
column before the drain -> first column after). A per-pass level on the board (memory-controllers ISSUE-007:
583 / 566 / 519 MB/s on the bank_interleave row-hit cells) is a cadence the stream locks into after a
refresh, not a per-refresh cost -- read the segments, not the gaps.

    dram_trace_segments.py trace.json [trace2.json ...]      the segment table per trace
    dram_trace_segments.py trace.json --dump FROM TO          the commands per cycle in [FROM, TO)

Method: vault/handbook/dv/dram-cycle-model.md (the 2026-11-23 section).
"""
from __future__ import annotations

import argparse
import bisect
import json
import sys
from collections import Counter
from typing import List, Sequence, Tuple

Event = Tuple[int, str, int, int]
COLS = ("RD", "WR")


def load(path: str) -> List[Event]:
    with open(path) as f:
        return [tuple(e) for e in json.load(f)]  # type: ignore[misc]


def refresh_drains(ev: Sequence[Event], within: int = 8) -> List[List[int]]:
    """Clusters of explicit PREs no more than `within` cycles apart: one per refresh under close page."""
    clusters: List[List[int]] = []
    for t in (e[0] for e in ev if e[1] == "PRE"):
        if clusters and t - clusters[-1][-1] <= within:
            clusters[-1].append(t)
        else:
            clusters.append([t])
    return clusters


def segment_table(path: str, ev: Sequence[Event]) -> None:
    cols = [e[0] for e in ev if e[1] in COLS]
    if not cols:
        print(f"{path}: no columns")
        return
    drains = refresh_drains(ev)
    edges = [cols[0]] + [c[0] for c in drains] + [cols[-1] + 1]
    acts = [e for e in ev if e[1] == "ACT"]
    print(f"{path}: {len(cols)} columns, {len(drains)} refresh drains "
          f"({Counter(len(c) for c in drains).most_common(3)} PREs per drain)")
    for k, (a, b) in enumerate(zip(edges, edges[1:])):
        i, j = bisect.bisect_left(cols, a), bisect.bisect_left(cols, b)
        n = j - i
        if n < 20:
            continue
        cadence = (cols[j - 1] - cols[i]) / (n - 1)
        phases = Counter(e[3] for e in acts if a <= e[0] < b)
        last_act: dict = {}
        act_to_col: Counter = Counter()
        for e in ev:
            if not (a <= e[0] < b):
                continue
            if e[1] == "ACT":
                last_act[e[2]] = e[0]
            elif e[1] in COLS and e[2] in last_act:
                act_to_col[e[0] - last_act[e[2]]] += 1
        gaps = Counter(cols[x + 1] - cols[x] for x in range(i, j - 1))
        print(f"  seg {k:2d} {a:7d}..{b:7d} cadence {cadence:.3f} cyc/col x{n:5d} "
              f"ACT lane {phases.get(1, 0):5d} main {phases.get(0, 0):3d} "
              f"ACT->col {sorted(act_to_col.items())[:4]} colgap {sorted(gaps.items())[:5]}")
    around = []
    for c in drains:
        i = bisect.bisect_left(cols, c[0])
        if 0 < i < len(cols):
            around.append(cols[i] - cols[i - 1])
    print(f"  gap around each refresh (last column -> first column, cycles): {around}")


def dump(ev: Sequence[Event], lo: int, hi: int) -> None:
    by_cycle: dict = {}
    for e in ev:
        if lo <= e[0] < hi:
            by_cycle.setdefault(e[0], []).append(f"{e[1]}{e[2]}" + ("'" if e[3] else ""))
    for c in range(lo, hi):
        print(c, " ".join(by_cycle.get(c, ["."])))


def main(argv: Sequence[str] | None = None) -> int:
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    ap.add_argument("traces", nargs="+")
    ap.add_argument("--dump", nargs=2, type=int, metavar=("FROM", "TO"),
                    help="print the commands per cycle in [FROM, TO) of the first trace instead of the table")
    args = ap.parse_args(argv)
    if args.dump:
        dump(load(args.traces[0]), *args.dump)
        return 0
    for path in args.traces:
        segment_table(path.split("/")[-1], load(path))
    return 0


if __name__ == "__main__":
    sys.exit(main())
