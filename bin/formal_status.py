#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
"""Measure the formal suite and report what actually runs.

FORMAL_PRIORITY.md's Status column was hand-maintained and was wrong in both
directions: modules listed PASSING whose task directory held no proof at all,
and modules listed PASSING whose proof had never once elaborated. A status
that is typed rather than measured drifts silently, because a stale row looks
exactly like a current one.

    python3 bin/formal_status.py --areas amba cdc common integ_common
    python3 bin/formal_status.py --inventory        # no runs: what EXISTS
    python3 bin/formal_status.py --markdown         # table for the tracker

Exit status is non-zero if any task fails, so this can gate CI.
"""
from __future__ import annotations

import argparse
import json
import os
import pathlib
import re
import signal
import subprocess
import sys
import time

ROOT = pathlib.Path(__file__).resolve().parent.parent
DEFAULT_AREAS = ["amba", "cdc", "common", "integ_common"]


def sby_tasks(sby: pathlib.Path) -> list[str]:
    """The [tasks] section, or a single unnamed run."""
    body = sby.read_text(errors="replace")
    m = re.search(r"^\[tasks\]\s*$(.*?)(?=^\[|\Z)", body, re.M | re.S)
    if not m:
        return [""]
    names = [ln.split()[0] for ln in m.group(1).splitlines() if ln.strip()
             and not ln.strip().startswith("#")]
    return names or [""]


def discover(areas):
    """Every task directory, and how it reads its RTL."""
    out = []
    for area in areas:
        adir = ROOT / "formal" / area
        if not adir.is_dir():
            continue
        for d in sorted(p for p in adir.iterdir() if p.is_dir()):
            sbys = sorted(d.glob("*.sby"))
            out.append({
                "area": area,
                "name": d.name,
                "dir": d,
                "sby": sbys[0] if sbys else None,
                # A task with its own Makefile runs sv2v first (flatten flow).
                "flow": "flatten" if (d / "Makefile").exists() else "direct",
                "tasks": sby_tasks(sbys[0]) if sbys else [],
            })
    return out


def run_task(entry, task, timeout):
    d, sby = entry["dir"], entry["sby"]
    if entry["flow"] == "flatten":
        cmd = ["make", "-C", str(d), task or "all"]
    else:
        cmd = ["sby", "-f", sby.name] + ([task] if task else [])
    t0 = time.time()
    # Own a process GROUP, not just a child. sby spawns solver processes that
    # outlive it; killing only the direct child leaves them running, and they
    # then compete with every task after this one -- so one slow proof skews
    # the timings of the whole sweep and can starve it outright.
    proc = subprocess.Popen(cmd, cwd=str(d), stdout=subprocess.PIPE,
                            stderr=subprocess.STDOUT, text=True,
                            start_new_session=True)
    try:
        blob = proc.communicate(timeout=timeout)[0]
    except subprocess.TimeoutExpired:
        try:
            os.killpg(os.getpgid(proc.pid), signal.SIGKILL)
        except (ProcessLookupError, PermissionError):
            proc.kill()
        proc.communicate()
        return "TIMEOUT", timeout
    m = re.findall(r"DONE \((PASS|FAIL|ERROR|UNKNOWN)", blob)
    if not m:
        return "NORESULT", time.time() - t0
    # a flatten `make all` runs several sby tasks; worst result wins
    for bad in ("ERROR", "FAIL", "UNKNOWN"):
        if bad in m:
            return bad, time.time() - t0
    return "PASS", time.time() - t0


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--areas", nargs="+", default=DEFAULT_AREAS)
    ap.add_argument("--inventory", action="store_true",
                    help="do not run anything; report what exists")
    ap.add_argument("--markdown", action="store_true")
    ap.add_argument("--json", metavar="PATH")
    ap.add_argument("--timeout", type=int, default=1500)
    ap.add_argument("--only", nargs="*", default=None)
    # Skip named tasks -- e.g. one already running in its own directory from a
    # separate long-budget job. Two sby runs writing the same <task>_prove/ dir
    # corrupt each other, and nothing in sby prevents it.
    ap.add_argument("--exclude", nargs="*", default=None)
    args = ap.parse_args()

    entries = discover(args.areas)
    if args.only:
        entries = [e for e in entries if e["name"] in args.only]
    if args.exclude:
        entries = [e for e in entries if e["name"] not in args.exclude]

    if args.inventory:
        print(f"{len(entries)} task directories under formal/{{{','.join(args.areas)}}}")
        for flow in ("flatten", "direct"):
            n = [e for e in entries if e["flow"] == flow and e["sby"]]
            print(f"  {flow:8s} {len(n)}")
        empty = [e for e in entries if not e["sby"]]
        if empty:
            print(f"  NO .sby  {len(empty)}: " + ", ".join(e["name"] for e in empty))
        return 0

    rows, bad = [], 0
    for i, e in enumerate(entries, 1):
        if not e["sby"]:
            rows.append({**{k: e[k] for k in ("area", "name", "flow")},
                         "task": "-", "status": "NOSBY", "secs": 0.0})
            bad += 1
            print(f"[{i}/{len(entries)}] {e['area']}/{e['name']}: NOSBY", file=sys.stderr)
            continue
        for task in e["tasks"]:
            st, secs = run_task(e, task, args.timeout)
            rows.append({**{k: e[k] for k in ("area", "name", "flow")},
                         "task": task or "(default)", "status": st, "secs": round(secs, 1)})
            if st != "PASS":
                bad += 1
            print(f"[{i}/{len(entries)}] {e['area']}/{e['name']} {task or ''}: {st} "
                  f"({secs:.0f}s)", file=sys.stderr)

    if args.json:
        pathlib.Path(args.json).write_text(json.dumps(rows, indent=1))

    tally = {}
    for r in rows:
        tally[r["status"]] = tally.get(r["status"], 0) + 1
    if args.markdown:
        print(f"<!-- generated by bin/formal_status.py on "
              f"{time.strftime('%Y-%m-%d')} -- do not hand-edit the Status column -->")
        print()
        print("| Area | Task | Flow | Result |")
        print("|---|---|---|---|")
        seen = {}
        for r in rows:
            k = (r["area"], r["name"])
            seen.setdefault(k, []).append(r["status"])
        for (area, name), sts in sorted(seen.items()):
            worst = next((s for s in ("NOSBY", "ERROR", "FAIL", "TIMEOUT",
                                      "NORESULT", "UNKNOWN") if s in sts), "PASS")
            flow = next(r["flow"] for r in rows if (r["area"], r["name"]) == (area, name))
            print(f"| {area} | {name} | {flow} | {worst} |")
        print()
    print("  ".join(f"{k}={v}" for k, v in sorted(tally.items())), file=sys.stderr)
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
