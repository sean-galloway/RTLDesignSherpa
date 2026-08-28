#!/usr/bin/env python3
"""Task-tracker integrity check for vault/Tasks/.

Three failure modes this catches, all of which have actually happened:

1. **Duplicate IDs within an area.** PUMICE-010/011 each name two unrelated
   tasks; PUMICE-008 exists as both a dropped task and a live open one.
   A bare `[[PUMICE-011]]` link is then ambiguous and the rollup counts lie.
2. **A stale `Next ID:` line.** Each area INDEX.md declares the next free
   number. If it is missing or <= the highest ID in use, the next person
   writing a task will collide again -- which is exactly how the pumice
   collisions happened.
3. **Status/page mismatch.** A task filed into closed.md whose body still
   says `**Status:** open`. Found on two pumice entries: filed but never
   re-statused, so they read as live work inside the closed page.

Historical collisions are grandfathered via KNOWN_COLLISIONS so the check
can be enforcing from day one without forcing a risky renumber of closed
history (renumbering breaks existing wikilinks). Anything NEW fails.

Usage:
    bin/check_task_ids.py                 # check every area
    bin/check_task_ids.py --area pumice   # one area
    bin/check_task_ids.py --next pumice   # print the next free ID and exit
"""
from __future__ import annotations

import argparse
import collections
import pathlib
import re
import subprocess
import sys

HEADING = re.compile(r"^#{2,3}\s+([A-Z][A-Z0-9]*-[A-Z0-9]+)\s*[—\-–]")
# Tolerant on purpose: the line is written by humans, so accept bold either
# side of the colon and any trailing prose after the ID.
NEXT_ID = re.compile(r"Next ID\**\s*:\s*\**\s*([A-Z][A-Z0-9]*-(\d+))")
STATUS = re.compile(r"^\*\*Status:\*\*\s*(\w+)", re.M)

# Pre-existing duplicates, recorded 2026-08-28. Grandfathered so the check
# can enforce immediately; do NOT add to this list to silence a new clash --
# renumber the new task instead (the whole point of the Next ID line).
KNOWN_COLLISIONS = {
    ("amba", "AMBA-INTEG"),
    ("common", "COMMON-021"),
    ("docs-review", "DOCREV-001"),
    ("pumice", "PUMICE-010"),
    ("pumice", "PUMICE-011"),
}

# closed.md / dropped.md bodies should not claim to be live.
TERMINAL_PAGES = {"closed.md": ("closed", "done", "resolved", "fixed"),
                  "dropped.md": ("dropped", "superseded", "wontfix")}


def repo_root() -> pathlib.Path:
    out = subprocess.check_output(["git", "rev-parse", "--show-toplevel"])
    return pathlib.Path(out.decode().strip())


def scan_area(area: pathlib.Path):
    """-> (ids{id: [loc]}, blocks[(id, page, status)])"""
    ids = collections.defaultdict(list)
    blocks = []
    for f in sorted(area.glob("*.md")):
        if f.name == "INDEX.md":
            continue
        lines = f.read_text().split("\n")
        for i, line in enumerate(lines, 1):
            m = HEADING.match(line)
            if not m:
                continue
            ids[m.group(1)].append(f"{f.name}:{i}")
            body = "\n".join(lines[i:i + 6])
            sm = STATUS.search(body)
            blocks.append((m.group(1), f.name, sm.group(1).lower() if sm else None))
    return ids, blocks


def highest(ids) -> int:
    nums = [int(m.group(1)) for i in ids for m in [re.search(r"-(\d+)$", i)] if m]
    return max(nums) if nums else 0


def check_area(area: pathlib.Path) -> tuple[list[str], list[str]]:
    """-> (errors, warnings). Errors block; warnings are reported only.

    Duplicate IDs and a stale Next ID are ERRORS: both are mechanical and
    both actively corrupt the tracker going forward. Status/page mismatch is
    a WARNING, because deciding whether a task filed in closed.md is 'really
    closed with a stale line' or 'still open and misfiled' needs a human who
    knows the work -- flipping the text automatically would launder open
    work into the closed pile, which is worse than the inconsistency.
    """
    errs: list[str] = []
    warns: list[str] = []
    ids, blocks = scan_area(area)

    # A directory with no numbered task headings is not a task AREA -- e.g.
    # vault/Tasks/projects/ holds handoff documents. Demanding an INDEX and a
    # Next ID line there is a false positive, and a checker that cries wolf
    # gets bypassed.
    if not ids:
        return errs, warns

    for tid, locs in sorted(ids.items()):
        if len(locs) > 1 and (area.name, tid) not in KNOWN_COLLISIONS:
            errs.append(f"{area.name}: DUPLICATE ID {tid} at {', '.join(locs)} "
                        f"-- renumber the newer one (see the Next ID line)")

    index = area / "INDEX.md"
    if not index.exists():
        errs.append(f"{area.name}: no INDEX.md")
    else:
        m = NEXT_ID.search(index.read_text())
        hi = highest(ids)
        if not m:
            errs.append(f"{area.name}: INDEX.md has no 'Next ID:' line "
                        f"(highest in use is {hi}); add one")
        elif int(m.group(2)) <= hi:
            errs.append(f"{area.name}: Next ID is {m.group(1)} but "
                        f"{hi} is already in use -- bump it past {hi}")

    for tid, page, status in blocks:
        want = TERMINAL_PAGES.get(page)
        if want and status and not status.startswith(want):
            warns.append(f"{area.name}: {tid} lives in {page} but its body says "
                         f"'**Status:** {status}' -- re-status it or move it")
    return errs, warns


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--area")
    ap.add_argument("--next", metavar="AREA",
                    help="print the next free ID for AREA and exit")
    args = ap.parse_args()

    tasks = repo_root() / "vault" / "Tasks"
    areas = [d for d in sorted(tasks.iterdir()) if d.is_dir()]
    if args.area:
        areas = [a for a in areas if a.name == args.area]

    if args.next:
        a = tasks / args.next
        ids, _ = scan_area(a)
        prefix = next((i.rsplit("-", 1)[0] for i in ids if re.search(r"-\d+$", i)),
                      args.next.upper())
        print(f"{prefix}-{highest(ids) + 1:03d}")
        return 0

    errs, warns = [], []
    for a in areas:
        e, w = check_area(a)
        errs += e
        warns += w

    if warns:
        print(f"Task-tracker warnings ({len(warns)}) -- not blocking:")
        for w in warns:
            print(f"  ? {w}")
        print()

    if errs:
        print(f"Task-tracker check FAILED ({len(errs)} issue(s)):\n", file=sys.stderr)
        for e in errs:
            print(f"  - {e}", file=sys.stderr)
        print("\nSee vault/Tasks/INDEX.md for the ID convention.", file=sys.stderr)
        return 1
    print(f"Task-tracker check passed ({len(areas)} area(s))")
    return 0


if __name__ == "__main__":
    sys.exit(main())
